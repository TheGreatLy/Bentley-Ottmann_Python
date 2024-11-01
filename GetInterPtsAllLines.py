"""
@Author       : yong.liu
@Date         : 2024-09-06 15:28:20
@LastEditors  : yong.liu
@LastEditTime : 2024-11-01 10:24:51
@FilePath     : GetInterPtsAllLines.py
@Description  : Bentley-Ottmann算法实现
"""
import heapq
import math
from collections import namedtuple, defaultdict
from sortedcontainers import SortedList

# 定义点、事件、活动线段列表等数据结构
Point = namedtuple('Point', 'x y')

class Segment:
    def __init__(self, start, end):
        self.start = start
        self.end = end
        # 默认使用start作为排序键
        self.key = self.start

    # 遇到交点更新排序键时调用
    def set_key(self, newkey):
        self.key = newkey
        # 更新所有引用该segment的事件
        # for event in self.events:
        #     event.segment = self

    def __lt__(self, other):
        # TODO 这个算法的关键点1，比较两个线段谁大谁小
        s1, s2 = self, other
        angle1 = calculate_angle_twoPts(*s1.start, *s1.end)
        angle2 = calculate_angle_twoPts(*s2.start, *s2.end)
        # 两条竖直线比较线段
        if angle1 == 90 and angle2 == 90:
            if s1.key.y < s2.key.y:
                return True
            elif s1.key.y == s2.key.y:
                return s1.end.y < s2.end.y
            else:
                return False
        
        # 如果是交点，则两个相同，相同情况下拿终点的y比较，跟其余线段比较还用key
        if s1.key == s2.key:
            return s1.end.y < s2.end.y

        # 其中一条为垂直线如何比较
        if angle1 != 90:
            slope1 = (s1.end.y - s1.start.y) / (s1.end.x - s1.start.x)
            b1 = s1.start.y - slope1 * s1.start.x
        else:
            slope2 = (s2.end.y - s2.start.y) / (s2.end.x - s2.start.x)
            b2 = s2.start.y - slope2 * s2.start.x
            if s1.key.y < (slope2 * s1.key.x + b2):
                return True
            elif s1.key.y == (slope2 * s1.key.x + b2):
                return s1.end.y < s2.end.y
            else:
                return False

        if angle2 != 90:
            slope2 = (s2.end.y - s2.start.y) / (s2.end.x - s2.start.x)
            b2 = s2.start.y - slope2 * s2.start.x
        else:
            slope1 = (s1.end.y - s1.start.y) / (s1.end.x - s1.start.x)
            b1 = s1.start.y - slope1 * s1.start.x
            if (slope1 * s2.key.x + b1) < s2.key.y:
                return True
            elif (slope1 * s2.key.x + b1) == s2.key.y:
                return s1.end.y < s2.end.y
            else:
                return False

        # 平行线如何比较线段大小
        if abs(angle1 - angle2) <= 1:
            x = min(s1.key.x, s2.key.x)
            y1 = x * slope1 + b1
            y2 = x * slope2 + b2
            if y1 < y2: return True
            elif y1 == y2: 
                if s1.end.y < s2.end.y: return True
                elif s1.end.y == s2.end.y:
                    if s1.start.x < s2.start.x: return True
                    elif s1.start.x == s2.start.x:
                        return s1.end.x < s2.end.x
                    else:
                        return False
                else:
                    return False
            else:
                return False

        # 最正常的两根斜线比较比较key所在的y谁大谁小
        if min(s2.key.x, s2.end.x) <= s1.key.x <= max(s2.key.x, s2.end.x):
            pre_y = slope2 * s1.key.x + b2
            if s1.key.y < pre_y:
                return True
            elif s1.key.y == pre_y:
                return s1.end.y < s2.end.y
            else:
                return False
        elif min(s1.key.x, s1.end.x) <= s2.key.x <= max(s1.key.x, s1.end.x):
            pre_y = slope1 * s2.key.x + b1
            if pre_y < s2.key.y:
                return True
            elif pre_y == s2.key.y:
                return s1.end.y < s2.end.y
            else:
                return False
        else:
            return s1.key.y < s2.key.y
    
    def __eq__(self, other) -> bool:
        return self.start == other.start and \
            self.end == other.end and \
                self.key == other.key

class EventType:
    START = 1
    END = 2
    INTERSECTION = 3

class Event:
    def __init__(self, x, point, event_type, segment=None):
        self.x = x  # 事件的x坐标
        self.p = point  # 事件的位置
        self.type = event_type  # 事件类型
        self.segment = segment  # 相关的线段（或交点时是两条线段）

    def __lt__(self, other):
        # 首先按 x 坐标排序，如果相同则按 y 坐标
        if self.x == other.x:
            return self.p.y < other.p.y
        return self.x < other.x

class BentleyOttmann:
    def __init__(self, segments):
        self.segments = segments
        self.event_queue = []
        self.active_segments = SortedList()  # 使用自定义方法排序
        self.intersections = []
        self.origin_seg2Newseg = defaultdict(int)
        self.visited_inter = defaultdict(int)

    def run(self):
        # 初始化事件队列
        for segment in self.segments:
            if segment.start.x > segment.end.x:
                segment = Segment(segment.end, segment.start)
            if segment.start.x == segment.end.x:
                if segment.start.y > segment.end.y:
                    segment = Segment(segment.end, segment.start)
            # 初始化记录线段字典，用于跟踪线段对象的变化
            if self.origin_seg2Newseg[((int(segment.start.x), int(segment.start.y)), 
                                       (int(segment.end.x), int(segment.end.y)))]: continue
            s_e = Event(segment.start.x, segment.start, EventType.START, segment)
            # segment.events.append(s_e)
            end_e = Event(segment.end.x, segment.end, EventType.END, segment)
            # segment.events.append(end_e)
            self.origin_seg2Newseg[((int(segment.start.x), int(segment.start.y)), 
                                    (int(segment.end.x), int(segment.end.y)))] = segment
            # 用最小堆记录事件，每次弹出堆顶最小事件（x排序）
            heapq.heappush(self.event_queue, s_e)
            heapq.heappush(self.event_queue, end_e)
        
        # 处理事件
        while self.event_queue:
            event = heapq.heappop(self.event_queue)
            if event.type == EventType.START:
                self.handle_start(event.segment)
            elif event.type == EventType.END:
                self.handle_end(event.segment)
            elif event.type == EventType.INTERSECTION:
                self.handle_intersection(event)

        return self.intersections

    def handle_start(self, segment):
        self.active_segments.add(segment)
        idx = self.active_segments.index(segment)
        if idx > 0:
            self.check_intersection(self.active_segments[idx - 1], segment)
        if idx < len(self.active_segments) - 1:
            self.check_intersection(segment, self.active_segments[idx + 1])

    def handle_end(self, segment):
        # 终点事件去除线段要去除最新的线段，可能segment是最原始的线段，
        # 会造成找不到index，因为扫描过程中会改变segment的key
        new_seg = self.origin_seg2Newseg[((int(segment.start.x), int(segment.start.y)), 
                                            (int(segment.end.x), int(segment.end.y)))]
        idx = self.active_segments.index(new_seg)
        prev_segment = self.active_segments[idx - 1] if idx > 0 else None
        next_segment = self.active_segments[idx + 1] if idx < len(self.active_segments) - 1 else None
        self.active_segments.remove(new_seg)
        if prev_segment and next_segment:
            self.check_intersection(prev_segment, next_segment)

    def handle_intersection(self, event):
        # 处理交点事件，交换活动线段顺序并检查新邻居的交点
        s1, s2 = event.segment
        if s1 in self.active_segments and s2 in self.active_segments:
            # 获取旧插入的位置
            oidx1 = self.active_segments.index(s1)
            oidx2 = self.active_segments.index(s2)
            # 删除旧的顺序
            self.active_segments.remove(s1)
            self.active_segments.remove(s2)
            
            if oidx1 < oidx2:
                # s1在前
                """
                TODO 该算法的关键点2，如何在平衡二叉树中准确进行s1和s2的局部交换，
                交换后s1\s2中间不会被插入其余元素，key改为交点，因为按照x从左往右扫描交点以前的不会再看，
                activte_segments的排序是按照交点后的线段大小来排列, 
                如何精准交换s1 s2 配合__lt__如果key相等，比较end.y, 如果之前s1 < s2 end 一定是s1 > s2 
                """
                s1.set_key(event.p)
                s2.set_key(event.p)

                self.active_segments.add(s2)
                self.active_segments.add(s1)
                # 获取新插入的位置
                idx1 = self.active_segments.index(s1)
                self.origin_seg2Newseg[((int(s1.start.x), int(s1.start.y)), 
                                        (int(s1.end.x), int(s1.end.y)))] = self.active_segments[idx1]
                idx2 = self.active_segments.index(s2)
                self.origin_seg2Newseg[((int(s2.start.x), int(s2.start.y)), 
                                        (int(s2.end.x), int(s2.end.y)))] = self.active_segments[idx2]

                # 交换后s2在前 检查邻接交点
                if idx2 > 0:
                    self.check_intersection(self.active_segments[idx2 - 1], s2)
                if idx1 < len(self.active_segments) - 1:
                    self.check_intersection(s1, self.active_segments[idx1 + 1])
            else:
                # s2在前
                s1.set_key(event.p)
                s2.set_key(event.p)
                self.active_segments.add(s2)
                self.active_segments.add(s1)
                # 获取新插入的位置
                idx1 = self.active_segments.index(s1)
                self.origin_seg2Newseg[((int(s1.start.x), int(s1.start.y)), 
                                        (int(s1.end.x), int(s1.end.y)))] = self.active_segments[idx1]
                idx2 = self.active_segments.index(s2)
                self.origin_seg2Newseg[((int(s2.start.x), int(s2.start.y)), 
                                        (int(s2.end.x), int(s2.end.y)))] = self.active_segments[idx2]

                # 交换后s1在前 检查邻接交点
                if idx1 > 0:
                    self.check_intersection(self.active_segments[idx1 - 1], s1)
                if idx2 < len(self.active_segments) - 1:
                    self.check_intersection(s2, self.active_segments[idx2 + 1])

        else:
            aaa = 1

    def check_intersection(self, s1, s2):
        # 计算过相交的两条线段不能再计算相交，
        # 也可以按照key->end这段计算交点就不会出现重复交点的问题，
        if self.visited_inter[((s1.start, s1.end), (s2.start, s2.end))] or \
            self.visited_inter[((s2.start, s2.end), (s1.start, s1.end))]:
            return
        self.visited_inter[((s1.start, s1.end), (s2.start, s2.end))] = 1
        # 检查两条线段是否相交
        p = self.get_intersection_point(s1, s2)
        if p:
            self.intersections.append(p)
            # 关键点3 这里int(p.x)是因为当遇到竖线情况下，float类型坐标可能交点x>竖线end事件x造成end先出队列，导致交点事件处理出错
            heapq.heappush(self.event_queue, Event(int(p.x), p, EventType.INTERSECTION, (s1, s2)))

    @staticmethod
    def get_intersection_point(s1, s2):
        """ 计算线段 s1 和 s2 的交点 """
        angle1 = calculate_angle_twoPts(*s1.start, *s1.end)
        angle2 = calculate_angle_twoPts(*s2.start, *s2.end)
        if abs(angle1 - angle2) <= 1: return None
        pt = intersect((s1.start, s1.end), (s2.start, s2.end))
        if pt:
            return Point(pt[0], pt[1])
        return pt

# 一些公用的函数
def line_intersection(A, B, C, D):
    a1 = B[1] - A[1]
    b1 = A[0] - B[0]
    c1 = a1 * A[0] + b1 * A[1]
  
    a2 = D[1] - C[1]
    b2 = C[0] - D[0]
    c2 = a2 * C[0] + b2 * C[1]
  
    determinant = a1 * b2 - a2 * b1
  
    if determinant == 0:
        return None  # lines are parallel
  
    x = (b2 * c1 - b1 * c2) / determinant
    y = (a1 * c2 - a2 * c1) / determinant

    if min(A[0], B[0]) <= x <= max(A[0], B[0]) and \
       min(A[1], B[1]) <= y <= max(A[1], B[1]) and \
       min(C[0], D[0]) <= x <= max(C[0], D[0]) and \
       min(C[1], D[1]) <= y <= max(C[1], D[1]):
        return (x, y)
    else:
        return None

def intersect(seg1, seg2):
	p = seg1[0]
	r = (seg1[1][0] - seg1[0][0], seg1[1][1] - seg1[0][1])
	q = seg2[0]
	s = (seg2[1][0] - seg2[0][0], seg2[1][1] - seg2[0][1])
	denom = r[0] * s[1] - r[1] * s[0]

	if denom == 0:
		return None
    
	numer = float(q[0] - p[0]) * s[1] - (q[1] - p[1]) * s[0]
	t = numer / denom

	numer = float(q[0] - p[0]) * r[1] - (q[1] - p[1]) * r[0]
	u = numer / denom

	if (t < 0 or t > 1) or (u < 0 or u > 1):
		return None
    
	x = p[0] + t * r[0]
	y = p[1] + t * r[1]

	return (x, y)

def calculateSlope(p1, p2):
    if abs(p1[0] - p2[0]) < 5:
        k = float('inf')
        return k
    else:
        k = (round(p1[1]) - round(p2[1])) / (round(p1[0]) - round(p2[0]))
        return k

def calculate_angle_twoPts(x1, y1, x2, y2):
    """
    计算两点之间的角度
    """
    slope = calculateSlope((x1, y1), (x2, y2))
    angle_radians = math.atan(slope)
    angle_degrees = math.degrees(angle_radians)
    return angle_degrees

__All__ = [Point, Segment, BentleyOttmann]

