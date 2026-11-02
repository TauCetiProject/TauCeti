/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.RingTheory.Trace.Regular

/-!
# Orders in finite-dimensional algebras

Let `R` be a domain with fraction field `F` and `E` a finite-dimensional `F`-algebra, not
necessarily commutative. An `R`-order in `E` is an `R`-subalgebra `Λ` of `E` which is an `R`-lattice
in `E` in the sense of `Submodule.IsLattice`: it is finitely generated as an `R`-module and spans
`E` over `F`. Orders are the integral structures on which arithmetic of `E` is done: the ring of
integers of a number field, group rings `R[G] ⊆ F[G]`, and `M_n(R) ⊆ M_n(F)` are orders.

Every element of an order is integral over `R`. Conversely, over an integrally closed noetherian
`R`, a spanning subalgebra all of whose elements are integral is an order provided the regular trace
form of `E` is nondegenerate: the regular traces of products of its elements lie in `R`, so the
subalgebra lies in the `R`-span of the dual basis of an `F`-basis chosen inside it. Some hypothesis
of this kind is needed: if `R` is not a field, then in `E = F[ε]/(ε²)` the subalgebra `R + F ε`
spans `E` and consists of integral elements, but is not finitely generated over `R`. The
regular-trace hypothesis is stronger than necessary: it excludes `M_p(F)` in characteristic `p`,
whose regular trace form vanishes, although the conclusion holds there via the reduced trace.

## Main definitions

* `TauCeti.IntegralOrder.IsOrder F Λ`: the `R`-subalgebra `Λ` of `E` is an `R`-order in `E`.
* `TauCeti.IntegralOrder.groupRingSubalgebra R F G`: the group ring `R[G]` as an `R`-subalgebra of
  `F[G]`.

## Main results

* `TauCeti.IntegralOrder.isOrder_iff`: `Λ` is an order iff it is finite over `R` and spans `E`.
* `TauCeti.IntegralOrder.IsOrder.isIntegral`: every element of an order is integral over `R`.
* `TauCeti.IntegralOrder.IsOrder.le_integralClosure`: in a commutative algebra, every order lies in
  the integral closure of `R`.
* `TauCeti.IntegralOrder.isOrder_of_isIntegral`: a spanning subalgebra of integral elements is an
  order when `R` is integrally closed and noetherian and the regular trace form is nondegenerate.
* `TauCeti.IntegralOrder.mem_groupRingSubalgebra`: `x ∈ F[G]` lies in `R[G]` iff all its
  coefficients come from `R`.
* `TauCeti.IntegralOrder.groupRing_isOrder`: `R[G]` is an order in `F[G]` for a finite monoid `G`.
* `TauCeti.IntegralOrder.integralClosure_isOrder`: the integral closure of an integrally closed
  noetherian `R` in a finite separable extension of `F` is an order.

## References

* H. Johnston, *Notes on Galois modules*, Definition 3.8 and Examples 3.10.
* J. Voight, *Quaternion algebras*, Definition 10.2.1 and Lemma 10.3.7; the integrality criterion
  is proved there for separable algebras with the reduced trace, and here with the regular trace.

The proof of `TauCeti.IntegralOrder.isOrder_of_isIntegral` follows Mathlib's
`IsIntegralClosure.range_le_span_dualBasis` and `IsIntegralClosure.isNoetherian`, which carry out
the dual-basis bound for the integral closure in a finite separable field extension.
-/

public section

open Module Submodule

namespace TauCeti.IntegralOrder

section Basic

variable {R : Type*} (F : Type*) {E : Type*} [CommRing R] [CommRing F] [Ring E]
  [Algebra R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]

/-- An `R`-subalgebra `Λ` of an `F`-algebra `E` is an `R`-order in `E` if it is an `R`-lattice in
`E`: finitely generated as an `R`-module, with `F`-span all of `E`. -/
def IsOrder (Λ : Subalgebra R E) : Prop :=
  (Subalgebra.toSubmodule Λ).IsLattice F

variable {F}

/-- Being an order is being an `R`-lattice in `E` (this is the definition of `IsOrder`). -/
theorem isOrder_iff_isLattice {Λ : Subalgebra R E} :
    IsOrder F Λ ↔ (Subalgebra.toSubmodule Λ).IsLattice F :=
  Iff.rfl

/-- An `R`-subalgebra is an order exactly when it is finite over `R` and spans `E` over `F`. -/
theorem isOrder_iff {Λ : Subalgebra R E} :
    IsOrder F Λ ↔ Module.Finite R Λ ∧ span F (Λ : Set E) = ⊤ :=
  ⟨fun h => ⟨.of_fg h.fg, h.span_eq_top⟩, fun h => ⟨Module.Finite.iff_fg.1 h.1, h.2⟩⟩

namespace IsOrder

variable {Λ Γ : Subalgebra R E}

/-- An order is finite as an `R`-module. -/
theorem finite (h : IsOrder F Λ) : Module.Finite R Λ :=
  (isOrder_iff.1 h).1

/-- An order spans its ambient algebra over `F`. -/
theorem span_eq_top (h : IsOrder F Λ) : span F (Λ : Set E) = ⊤ :=
  (isOrder_iff.1 h).2

/-- **Elements of orders are integral.** Every element of an `R`-order is integral over `R`, since
the order is a finitely generated `R`-module. -/
theorem isIntegral (h : IsOrder F Λ) {x : E} (hx : x ∈ Λ) : IsIntegral R x :=
  IsIntegral.of_mem_of_fg Λ (Module.Finite.iff_fg.1 h.finite) x hx

/-- A finitely generated subalgebra containing an order is an order. -/
theorem of_le (h : IsOrder F Λ) (hle : Λ ≤ Γ) [Module.Finite R Γ] : IsOrder F Γ :=
  have : (Subalgebra.toSubmodule Λ).IsLattice F := h
  isOrder_iff_isLattice.2 <|
    IsLattice.of_le_of_isLattice_of_fg F (Subalgebra.toSubmodule.monotone hle)
      (Module.Finite.iff_fg.1 inferInstance)

end IsOrder

omit [Algebra F E] [Algebra R E] [IsScalarTower R F E] in
/-- The image of `R` is an `R`-order in `F`. -/
theorem isOrder_bot : IsOrder F (⊥ : Subalgebra R F) := by
  refine isOrder_iff.2 ⟨inferInstance, eq_top_iff.2 fun x _ => ?_⟩
  simpa using smul_mem (span F ((⊥ : Subalgebra R F) : Set F)) x
    (subset_span (one_mem (⊥ : Subalgebra R F)))

end Basic

section Commutative

variable {R F E : Type*} [CommRing R] [CommRing F] [CommRing E]
  [Algebra R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]

/-- In a commutative algebra, every `R`-order lies in the integral closure of `R`. -/
theorem IsOrder.le_integralClosure {Λ : Subalgebra R E} (h : IsOrder F Λ) :
    Λ ≤ integralClosure R E :=
  fun _ hx => h.isIntegral hx

end Commutative

section Integral

variable {R F E : Type*} [CommRing R] [Field F] [Ring E]
  [Algebra R F] [IsFractionRing R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [FiniteDimensional F E]

/-- **Integral spanning subalgebras are orders.** Let `R` be an integrally closed noetherian domain
with fraction field `F`, and `E` a finite-dimensional `F`-algebra whose regular trace form
`(x, y) ↦ Tr_F (x * y)` is nondegenerate. An `R`-subalgebra of `E` spanning `E` over `F` and
consisting of elements integral over `R` is an `R`-order in `E`. -/
theorem isOrder_of_isIntegral [IsIntegrallyClosed R] [IsNoetherianRing R]
    (hB : (Algebra.regularTraceForm F E).Nondegenerate) {Λ : Subalgebra R E}
    (hint : ∀ x ∈ Λ, IsIntegral R x) (hspan : span F (Λ : Set E) = ⊤) : IsOrder F Λ := by
  classical
  -- an `F`-basis `b` of `E` made of elements of `Λ`, and its dual basis `d`
  obtain ⟨s, hsΛ, hs, hli⟩ := exists_linearIndependent F (Λ : Set E)
  have : Fintype s := hli.setFinite.fintype
  let b : Basis s F E := Basis.mk hli (by rw [Subtype.range_coe, hs, hspan])
  have hb : ∀ i, b i ∈ Λ := fun i => by
    rw [Basis.mk_apply]
    exact hsΛ i.2
  let d := (Algebra.regularTraceForm F E).dualBasis hB b
  -- `Λ` lies in the `R`-span of `d`: the `d`-coordinates of `x ∈ Λ` are regular traces of
  -- elements `x * b i` of `Λ`, which are integral over `R` and lie in `F`, hence in `R`
  have hle : Subalgebra.toSubmodule Λ ≤ span R (Set.range d) := fun x hx => by
    rw [← d.sum_repr x]
    refine sum_mem fun i _ => ?_
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 <|
      Algebra.isIntegral_trace_lmul (K := F) <|
        hint _ (Λ.mul_mem hx (hb i))
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.regularTraceForm_apply, ← hr,
      algebraMap_smul]
    exact smul_mem _ r (subset_span ⟨i, rfl⟩)
  exact isOrder_iff.2 ⟨Module.Finite.iff_fg.2 ((fg_span (Set.finite_range d)).of_le hle), hspan⟩

/-- **Integral closures are orders.** The integral closure of an integrally closed noetherian domain
`R` in a finite separable extension `L` of its fraction field `F` is an `R`-order in `L`. -/
theorem integralClosure_isOrder [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (L : Type*) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] : IsOrder F (integralClosure R L) := by
  refine isOrder_iff.2 ⟨IsIntegralClosure.finite R F L (integralClosure R L),
    eq_top_iff.2 fun x _ => ?_⟩
  -- some nonzero `y : R` makes `y • x` integral, and then `x = y⁻¹ • (y • x)`
  obtain ⟨y, hy, hyx⟩ := exists_integral_multiples R F (L := L) {x}
  have hy' : algebraMap R F y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hy
  have hmem : y • x ∈ span F (integralClosure R L : Set L) :=
    subset_span (hyx x (Finset.mem_singleton_self x))
  convert smul_mem _ (algebraMap R F y)⁻¹ hmem using 1
  rw [← algebraMap_smul F y x, smul_smul, inv_mul_cancel₀ hy', one_smul]

end Integral

section GroupRing

open MonoidAlgebra

variable (R F G : Type*) [CommRing R] [CommRing F] [Algebra R F] [Monoid G]

/-- The group ring `R[G]` as an `R`-subalgebra of `F[G]`: the image of the map `R[G] → F[G]`
applying `algebraMap R F` to every coefficient. -/
noncomputable def groupRingSubalgebra : Subalgebra R (MonoidAlgebra F G) :=
  (mapAlgHom G (Algebra.ofId R F)).range

variable {R F G}

/-- An element of `F[G]` lies in `R[G]` exactly when all its coefficients come from `R`. -/
@[simp]
theorem mem_groupRingSubalgebra {x : MonoidAlgebra F G} :
    x ∈ groupRingSubalgebra R F G ↔ ∀ g, x.coeff g ∈ (algebraMap R F).range := by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ g
    exact ⟨y.coeff g, by simp⟩
  · rw [← sum_coeff_single x]
    refine sum_mem fun g _ => ?_
    obtain ⟨r, hr⟩ := hx g
    exact ⟨single g r, by simp [hr]⟩

/-- The basis element `g` of `F[G]` lies in `R[G]`. -/
theorem single_one_mem_groupRingSubalgebra (g : G) :
    single g (1 : F) ∈ groupRingSubalgebra R F G :=
  mem_groupRingSubalgebra.2 fun h => by
    classical
    rw [coeff_single, Finsupp.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]

variable (R F G) in
/-- As an `R`-module, `R[G]` is spanned by the basis elements `g` of `F[G]`. -/
theorem toSubmodule_groupRingSubalgebra :
    Subalgebra.toSubmodule (groupRingSubalgebra R F G) =
      span R (Set.range fun g : G => single g (1 : F)) := by
  refine le_antisymm (fun x hx => ?_) <|
    span_le.2 <| Set.range_subset_iff.2 single_one_mem_groupRingSubalgebra
  rw [Subalgebra.mem_toSubmodule, mem_groupRingSubalgebra] at hx
  rw [← sum_coeff_single x]
  refine sum_mem fun g _ => ?_
  obtain ⟨r, hr⟩ := hx g
  rw [← hr, Algebra.algebraMap_eq_smul_one, ← smul_single]
  exact smul_mem _ r (subset_span ⟨g, rfl⟩)

variable (R F G) in
/-- **Group rings are orders.** For a finite monoid `G`, the group ring `R[G]` is an `R`-order in
`F[G]`. -/
theorem groupRing_isOrder [Finite G] : IsOrder F (groupRingSubalgebra R F G) := by
  refine isOrder_iff_isLattice.2 ⟨?_, eq_top_iff.2 ?_⟩
  · rw [toSubmodule_groupRingSubalgebra]
    exact fg_span (Set.finite_range _)
  · rw [← (MonoidAlgebra.basis G F).span_eq]
    exact span_mono <| Set.range_subset_iff.2 fun g => by
      simpa using single_one_mem_groupRingSubalgebra (R := R) g

end GroupRing

end TauCeti.IntegralOrder
