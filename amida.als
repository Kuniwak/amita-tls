// あみだくじの縦線の位置。
abstract sig End {}
one sig Left extends End {}
sig NotLeft extends End {
	nextEnd: one End
}

// End は分岐や孤立グラフのない一本のグラフ上に並ぶ。
fact {
	one e: End | e.^nextEnd = End - e
}

// あみだくじの縦線上の高さ。
abstract sig Height {}
one sig Top extends Height {}
sig NotTop extends Height {
	below: one Height
}

// 高さは分岐や孤立グラフのない一本のグラフ上に並ぶ。
fact {
	one h: Height | h.^below = Height - h
}

// あみだくじの2つの縦線を接続する線分。
sig Bar {
	// 左端が接続される列の位置。
	left: one End,
	// 左端が接続される列の高さ。
	leftHeight: one Height,
	// 右端が接続される列の位置。
	right: one End,
	// 右端が接続される列の高さ。
	rightHeight: one Height,
}

fact {
	// ある軸について、左右いずれかからある高さで接続される bar は高々1つである。
	all e: End, h: Height | lone b: Bar |
		(left.e = b and leftHeight.h = b) or (right.e = b and rightHeight.h = b)
}

sig Answer {
	way: Height one -> one End
}

sig AnswerStep {
	start: one End
	startHeight: one Height
	end: one End
	endHeight: one Height
}

pred solve(e: End) {
	all h: NotTop | some s: AnswerStep | goto[s, 
}

pred goto(s: AnswerStep, e: End, h: Height) {
	gotoRight[s, e, h] or gotoLeft[s, e, h] or gotoDown[s, e, h]
}

pred gotoRight(s: AnswerStep, e: End, h: Height) {
	one b: Bar | (b.left = e and b.leftHeight = h)
			and (s.start = e and s.startHeight = h and s.end = b.right and s.endHeight = below.(b.rightHeight))
}

pred gotoLeft(s: AnswerStep, e: End, h: Height) {
	one b: Bar | (b.right = e and b.rightHeight = h)
		and (s.start = e and s.startHeight = h and s.end = b.left and s.endHeight = below.(b.leftHeight))
}

pred gotoDown(s: AnswerStep, e: End, h: Height) {
	(no b: Bar | b.left = e or b.right = e)
		and (s.start = e and s.startHeight = h and s.end = e and s.endHeight = below.h)	
}

run simulate for 10 but exactly 5 End
