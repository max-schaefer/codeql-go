package main

func taint() string {
	return "tainted"
}

func sink(arg interface{}) {}

func step(s string) string {
	return s
}

type box struct {
	s string
}

func NewBox(s string) *box {
	return &box{s: s}
}

func (b *box) getS1() string {
	return b.s
}

func (b *box) getS2() string {
	return step(b.s)
}

func (b *box) setS1(s string) {
	b.s = s
}

func (b *box) setS2(s string) {
	b.s = step(s)
}

func mk(s string) *box {
	b := NewBox("")
	b.s = step(s)
	return b
}

func foo(b1, b2 *box) {
	b1.setS1(taint())
	sink(b1.getS1())

	b2.setS2(taint())
	sink(b2.getS2())

	t3 := taint()
	b3 := NewBox(step(t3))
	sink(b3.s)

	b4 := mk(taint())
	sink(b4.getS1())
}
