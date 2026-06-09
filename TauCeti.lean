-- This is the AI-owned root of the TauCeti mathematics library.
--
-- Everything reachable from here must be sorry-free, and must not import
-- `TauCetiRoadmap` or `TauCetiReview` (both enforced in CI). As the library
-- grows, import the submodules of `TauCeti/` here.
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat
import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
import TauCeti.Algebra.Coalgebra.Comodule.Hom
import TauCeti.Algebra.Coalgebra.Comodule.Trivial
import TauCeti.Algebra.Coalgebra.ComoduleCat
import TauCeti.AlgebraicGeometry.WeilDivisor
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber
import TauCeti.AlgebraicTopology.UniversalCover.Deck.FiberTransport
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular
import TauCeti.Analysis.PDE.UniformEllipticity
import TauCeti.Basic
