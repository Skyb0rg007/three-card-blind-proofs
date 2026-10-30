
# three-card-blink-proofs

This repo contains a mechanization of the famous open problem in
MTG three-card blind.

## The background

[Three card blind](https://www.3cardblind.com/) is a MTG format where each
player has perfect info, and matchups are resolved by playing the game
optimally.

One matchup complicated things so much that it became impossible to determine,
resulting in a card banning.

## The matchup

Player A has the deck:

- [Hangarback Walker][]
- [Hangarback Walker][]
- [City of Traitors][]

Player B has the deck:

- [Hangarback Walker][]
- [Elixir of Immortality][]
- [City of Traitors][]

The goal: determine whether either player has a winning strategy (both when
Player A starts and when Player B starts).

The official channel made a YouTube video on the topic [here](https://youtu.be/hdaiKwKN50U).

## This repo

This repo contains a [Rocq][] mechanization of the problem and a proof of the solution.

[Hangarback Walker]: https://scryfall.com/card/soc/348/hangarback-walker
[City of Traitors]: https://scryfall.com/card/tpr/237/city-of-traitors
[Elixir of Immortality]: https://scryfall.com/card/c21/243/elixir-of-immortality
[Rocq]: https://rocq-prover.org
