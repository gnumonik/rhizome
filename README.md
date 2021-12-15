# rhizome

Work in progress / highly experimental / subject to massive changes.


Embedded DSL for object oriented programming in Haskell, backed by row types. The primary goal of this project is to implement an OOP framework in which subtyping, inheritance, subclassing/superclassing, interfaces, and behavior are all clearly delineated from each other and explicitly represented in the types. 


The core framework is an adaptation of Purescript's Halogen library with substantial alterations and extensions. A "traditional OOP" layer rests on top of the core framework and supports (or will, when it's done!) the idiomatic OOP forms that Haskellers know and hate. 


At the moment the core framework is implemented (see Data.Rhizome.Example for a very simple counter example, or Data.Rhizome.Container for a significantly more complex "higher order" example). The foundation for the fully featured "traditional OOP mode" is mostly implemented but needs a significant amount of work in terms of UX. 

Note: This project aims at exploring the design space for OOP features in a type safe manner inside a pure functional language with bounded quantification, (some) dependently typed features, and (via a library) row polymorphism. In other words, it is not intended to allow you to write Java or Python or C++ in Haskell. But, if you *have a problem where an object oriented solution is the most natural solution* **and** *you require a level of type safety that is not possible in a traditional OOP language* then this might be something worth considering. (When it's done.)

