/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocallyCompact
public import TauCeti.Topology.Algebra.RestrictedProduct.SecondCountable
public import TauCeti.Topology.Instances.Matrix

/-!
# Second countability and Borel structures on adeles and ideles

For a number field `K`, the finite adele ring `𝔸_{K,f}`, the infinite adele ring `K_∞`, the adele
ring `𝔸_K = K_∞ × 𝔸_{K,f}`, their unit groups (the finite ideles and the ideles), and the groups
`GL_n` over each of these rings are second countable. This file registers these instances and
the Borel structures on which the Haar measures of adeles and ideles live.

* The maximal ideals of `𝓞 K` form a countable set, since every ideal of the countable noetherian
  ring `𝓞 K` is spanned by a finite subset.
* Each completion `K_v` at a finite place is a nonarchimedean local field, hence second countable,
  and its integer ring is open; so the restricted product `𝔸_{K,f}` over the countable set of
  finite places is second countable.
* `K_∞` is homeomorphic to the Minkowski space `ℝ^{r₁} × ℂ^{r₂}`.
* The unit group of a second-countable topological monoid `M` is second countable: it carries
  the topology making `u ↦ (u, u⁻¹)` an embedding into `M × Mᵐᵒᵖ`. This also covers the adelic
  rings, whose unit groups do not carry the subspace topology.

The local completions `K_v`, the finite adeles, the infinite adeles, the ideles and the finite
ideles carry their Borel σ-algebras; the adele ring carries the product σ-algebra of
`K_∞ × 𝔸_{K,f}`, which is its Borel σ-algebra by second countability
(`NumberField.AdeleRing.instBorelSpace`).

## Main results

* `IsDedekindDomain.HeightOneSpectrum.countable_of_countable`: a countable Dedekind domain has
  countably many maximal ideals; `NumberField.instCountableHeightOneSpectrum` for `𝓞 K`.
* `TauCeti.instSecondCountableTopologyUnits`: units of a second-countable topological monoid;
  with Tau Ceti's second countability of matrix spaces this makes `GL_n` over each adelic ring
  second countable.
* `IsDedekindDomain.FiniteAdeleRing.instSecondCountableTopology`,
  `NumberField.InfiniteAdeleRing.instSecondCountableTopology`,
  `NumberField.AdeleRing.instSecondCountableTopology`.
* `IsDedekindDomain.HeightOneSpectrum.instBorelSpaceAdicCompletion`,
  `IsDedekindDomain.FiniteAdeleRing.instBorelSpace`,
  `NumberField.InfiniteAdeleRing.instBorelSpace`, `NumberField.AdeleRing.instBorelSpace`,
  `NumberField.IdeleGroup.instBorelSpace`, `IsDedekindDomain.FiniteAdeleRing.instBorelSpaceUnits`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., Lemma 3.63, pp. 188–189 (the countable restricted-product topology).
-/

public section

noncomputable section

open IsDedekindDomain MeasureTheory NumberField TopologicalSpace

/-! ### Countability of the finite places -/

/-- A countable Dedekind domain has countably many maximal ideals: every ideal is spanned by a
finite subset, and an ideal is determined by any finite set spanning it. -/
theorem IsDedekindDomain.HeightOneSpectrum.countable_of_countable (R : Type*) [CommRing R]
    [IsDedekindDomain R] [Countable R] : Countable (HeightOneSpectrum R) := by
  classical
  have hfg (v : HeightOneSpectrum R) : v.asIdeal.FG := IsNoetherian.noetherian v.asIdeal
  refine Function.Injective.countable (f := fun v ↦ (hfg v).choose) fun v w h ↦ ?_
  refine HeightOneSpectrum.ext ?_
  rw [← (hfg v).choose_spec, ← (hfg w).choose_spec]
  exact congrArg (fun s : Finset R ↦ Submodule.span R (s : Set R)) h

/-- A number field has countably many finite places. -/
instance NumberField.instCountableHeightOneSpectrum (K : Type*) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) :=
  have : Countable (𝓞 K) := Countable.of_moduleFinite (R := ℤ)
  HeightOneSpectrum.countable_of_countable (𝓞 K)

/-! ### Units of a second-countable monoid -/

/-- The unit group of a second-countable topological monoid is second countable: `u ↦ (u, u⁻¹)`
embeds it into `M × Mᵐᵒᵖ`. -/
instance TauCeti.instSecondCountableTopologyUnits {M : Type*} [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ :=
  have : SecondCountableTopology Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

/-! ### Second countability of the adeles -/

namespace IsDedekindDomain.FiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K]

/-- The finite adele ring of a number field is second countable. -/
instance instSecondCountableTopology : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.secondCountableTopology_of_cofinite
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (A := fun v ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (.of_forall fun _ ↦ Valued.isOpen_valuationSubring _)

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The infinite adele ring of a number field is second countable, being homeomorphic to the
Minkowski space. -/
instance InfiniteAdeleRing.instSecondCountableTopology :
    SecondCountableTopology (InfiniteAdeleRing K) :=
  (InfiniteAdeleRing.homeomorphMixedSpace K).secondCountableTopology

/-- The adele ring of a number field is second countable. -/
instance AdeleRing.instSecondCountableTopology :
    SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

end NumberField

/-! ### Borel structures -/

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The Borel σ-algebra on the completion `K_v`. -/
instance instMeasurableSpaceAdicCompletion : MeasurableSpace (v.adicCompletion K) := borel _

instance instBorelSpaceAdicCompletion : BorelSpace (v.adicCompletion K) := ⟨rfl⟩

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.FiniteAdeleRing

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The Borel σ-algebra on the finite adele ring. It is the Borel σ-algebra of the underlying
restricted product (`RestrictedProduct.measurableSpace`). -/
instance instMeasurableSpace : MeasurableSpace (FiniteAdeleRing R K) := borel _

instance instBorelSpace : BorelSpace (FiniteAdeleRing R K) := ⟨rfl⟩

/-- The Borel σ-algebra on the finite ideles. -/
instance instMeasurableSpaceUnits : MeasurableSpace (FiniteAdeleRing R K)ˣ := borel _

instance instBorelSpaceUnits : BorelSpace (FiniteAdeleRing R K)ˣ := ⟨rfl⟩

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The Borel σ-algebra on the infinite adele ring. -/
instance InfiniteAdeleRing.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing K) := borel _

instance InfiniteAdeleRing.instBorelSpace : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩

/-- The adele ring `K_∞ × 𝔸_{K,f}` carries the product σ-algebra. -/
instance AdeleRing.instMeasurableSpace : MeasurableSpace (AdeleRing R K) :=
  inferInstanceAs <| MeasurableSpace (InfiniteAdeleRing K × FiniteAdeleRing R K)

/-- The Borel σ-algebra on the idele group. -/
instance IdeleGroup.instMeasurableSpace : MeasurableSpace (IdeleGroup R K) := borel _

instance IdeleGroup.instBorelSpace : BorelSpace (IdeleGroup R K) := ⟨rfl⟩

/-- The product σ-algebra on the adele ring of a number field is its Borel σ-algebra. -/
instance AdeleRing.instBorelSpace [NumberField K] : BorelSpace (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

end NumberField
