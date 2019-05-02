from pyswip import Prolog
import curses

def fasill():
	pl = Prolog()
	pl.consult("src/fasill.pl")
	pl.consult("src/parser.pl")
	pl.consult("src/environment.pl")
	pl.consult("src/semantics.pl")
	list(pl.query("initialize([])"))
	stdscr = curses.initscr()
	stdscr.keypad(True)
	stdscr.scrollok(True)
	stdscr.clear()
	curses.noecho()
	i = 0
	while True:
		goal = ""
		i += 1
		stdscr.addstr("fasill:%d> " % i)
		stdscr.refresh()
		c = stdscr.getch()
		while c != 10 and c != curses.KEY_ENTER:
			goal += unichr(c)
			c = stdscr.getch()
		stdscr.addstr(goal + "\n")
		stdscr.refresh()
		query = pl.query("""
			atom_chars('%s', Chars),
			parse_query(Chars, Goal),
			query(Goal, SFCA),
			once(print_term(SFCA))
		""" % goal)
		for answer in query:
			stdscr.addstr("\n")
			stdscr.refresh()
			c = stdscr.getch()
	stdscr.keypad(False)
	curses.echo()
	curses.endwin()

fasill()