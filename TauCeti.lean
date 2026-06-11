-- This is the AI-owned root of the TauCeti mathematics library.
--
-- Everything reachable from here must be sorry-free, and must not import
-- `TauCetiRoadmap` or `TauCetiReview` (both enforced in CI). As the library
-- grows, import the submodules of `TauCeti/` here.
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.FiniteTypeCommHopfAlgCat
import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
import TauCeti.Algebra.Coalgebra.Comodule.Finite
import TauCeti.Algebra.Coalgebra.Comodule.FiniteCorestrict
import TauCeti.Algebra.Coalgebra.Comodule.FiniteTrivial
import TauCeti.Algebra.Coalgebra.Comodule.Hom
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficientAdjoin
import TauCeti.Algebra.Coalgebra.Comodule.Preadditive
import TauCeti.Algebra.Coalgebra.Comodule.Regular
import TauCeti.Algebra.Coalgebra.Comodule.Transport
import TauCeti.Algebra.Coalgebra.Comodule.Trivial
import TauCeti.Algebra.Coalgebra.Comodule.Zero
import TauCeti.Algebra.Coalgebra.ComoduleCat
import TauCeti.Algebra.Coalgebra.Subcoalgebra
import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
import TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice
import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map
import TauCeti.AlgebraicGeometry.WeilDivisor
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber
import TauCeti.AlgebraicTopology.UniversalCover.Deck.FiberOrbit
import TauCeti.AlgebraicTopology.UniversalCover.Deck.FiberTransport
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular
import TauCeti.Analysis.PDE.LowerOrder
import TauCeti.Analysis.PDE.UniformEllipticity
import TauCeti.Basic
