from pyswip import Prolog
import curses

def fasill():
	pl = Prolog()
	pl.consult("src/fasill.pl")
	pl.consult("src/parser.pl")
	pl.consult("src/environment.pl")
	pl.consult("src/semantics.pl")
	stdscr = curses.initscr()
	stdscr.keypad(True)
	stdscr.clear()
	curses.noecho()
	while True:
		goal = ""
		c = stdscr.getch()
		while c != 10 and c != curses.KEY_ENTER:
			goal += chr(c)
			c = stdscr.getch()
		stdscr.addstr(goal)
		stdscr.refresh()
		query = pl.query("""
			atom_chars('%s', Chars),
			parse_query(Chars, Goal),
			query(Goal, SFCA),
			once(print_term(SFCA))
		""" % goal)
		for answer in query:
			stdscr.addstr(str(answer))
			stdscr.refresh()
	stdscr.keypad(False)
	curses.echo()
	curses.endwin()

fasill()