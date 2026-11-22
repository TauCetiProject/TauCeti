/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Matrix
public import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Lattice
public import TauCeti.RingTheory.Trace.Regular
import TauCeti.RingTheory.IntegralClosure.TensorProduct

/-!
# Orders in finite-dimensional algebras

Let `R` be a domain with fraction field `F` and `E` a finite-dimensional `F`-algebra, not
necessarily commutative. An `R`-order in `E` is an `R`-subalgebra `Λ` of `E` which is an `R`-lattice
in `E`: it is finitely generated as an `R`-module and spans `E` over `F` (over a fraction field
`F`, this is `Submodule.IsFullLattice`). Orders are the integral structures on which arithmetic of
`E` is done: the ring of integers of a number field, group rings `R[G] ⊆ F[G]`, and
`M_n(R) ⊆ M_n(F)` are orders.

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
* `TauCeti.IntegralOrder.isOrder_op_iff`: `Λᵒᵖ` is an order in `Eᵐᵒᵖ` iff `Λ` is an order in `E`.
* `TauCeti.IntegralOrder.IsOrder.isIntegral`: every element of an order is integral over `R`.
* `TauCeti.IntegralOrder.not_isOrder_top_rat`: `ℚ` is not a `ℤ`-order in itself.
* `TauCeti.IntegralOrder.IsOrder.le_integralClosure`: in a commutative algebra, every order lies in
  the integral closure of `R`.
* `TauCeti.IntegralOrder.toSubmodule_le_dualSubmodule_regularTraceForm`: over an integrally closed
  `R`, a subalgebra of integral elements lies in its own dual for the regular trace form.
* `TauCeti.IntegralOrder.toSubmodule_le_span_dualBasis`: such a subalgebra containing an `F`-basis
  `b` of `E` lies in the `R`-span of the regular-trace dual basis of `b`.
* `TauCeti.IntegralOrder.isOrder_of_isIntegral`: a spanning subalgebra of integral elements is an
  order when `R` is integrally closed and noetherian and the regular trace form is nondegenerate.
* `TauCeti.IntegralOrder.mem_groupRingSubalgebra`: `x ∈ F[G]` lies in `R[G]` iff all its
  coefficients come from `R`.
* `TauCeti.IntegralOrder.groupRing_isOrder`: `R[G]` is an order in `F[G]` for a finite monoid `G`.
* `TauCeti.IntegralOrder.IsOrder.matrix`: if `Λ` is an order in `E`, the matrices with entries in
  `Λ` form an order in `Matrix n n E`; in particular `M_n(R)` is an order in `M_n(F)`.
* `TauCeti.IntegralOrder.integralClosure_isOrder`: the integral closure of an integrally closed
  noetherian `R` in a finite separable extension of `F` is an order.

## References

* H. Johnston, *Notes on Galois modules*, Definition 3.8 and Examples 3.10.
* J. Voight, *Quaternion algebras*, Definition 10.2.1 and Lemma 10.3.7; the integrality criterion
  is proved there for separable algebras with the reduced trace, and here with the regular trace.

`TauCeti.IntegralOrder.toSubmodule_le_span_dualBasis` and the proof of
`TauCeti.IntegralOrder.isOrder_of_isIntegral` follow Mathlib's
`IsIntegralClosure.range_le_span_dualBasis` and `IsIntegralClosure.isNoetherian`, which carry out
the dual-basis bound for the integral closure in a finite separable field extension.
-/

public section

open Module Submodule

namespace TauCeti.IntegralOrder

section Basic

variable {R : Type*} (F : Type*) {E : Type*} [CommRing R] [CommRing F] [Ring E]
  [Algebra F E] [Algebra R E]

/-- An `R`-subalgebra `Λ` of an `F`-algebra `E` is an `R`-order in `E` if it is an `R`-lattice in
`E`: finitely generated as an `R`-module, with `F`-span all of `E`. -/
def IsOrder (Λ : Subalgebra R E) : Prop :=
  (Subalgebra.toSubmodule Λ).FG ∧ span F (Λ : Set E) = ⊤

variable {F}

/-- An `R`-subalgebra is an order exactly when it is finite over `R` and spans `E` over `F`. -/
theorem isOrder_iff {Λ : Subalgebra R E} :
    IsOrder F Λ ↔ Module.Finite R Λ ∧ span F (Λ : Set E) = ⊤ :=
  ⟨fun h => ⟨.of_fg h.1, h.2⟩, fun h => ⟨Module.Finite.iff_fg.1 h.1, h.2⟩⟩

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
theorem of_le (h : IsOrder F Λ) (hle : Λ ≤ Γ) [Module.Finite R Γ] : IsOrder F Γ := by
  refine isOrder_iff.2 ⟨inferInstance, ?_⟩
  rw [eq_top_iff, ← h.span_eq_top]
  exact span_mono fun _ hx => hle hx

end IsOrder

/-- **Opposite orders.** `Λᵒᵖ` is an `R`-order in `Eᵐᵒᵖ` exactly when `Λ` is an `R`-order in `E`. -/
theorem isOrder_op_iff {Λ : Subalgebra R E} : IsOrder F Λ.op ↔ IsOrder F Λ := by
  have hspan : span F (Λ.op : Set Eᵐᵒᵖ) =
      (span F (Λ : Set E)).map ((MulOpposite.opLinearEquiv F : E ≃ₗ[F] Eᵐᵒᵖ) : E →ₗ[F] Eᵐᵒᵖ) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    simp [← MulOpposite.unop_inj]
  rw [isOrder_iff, isOrder_iff, hspan, Submodule.map_eq_top_iff,
    Module.Finite.equiv_iff Λ.linearEquivOp]

omit [Algebra F E] [Algebra R E] in
/-- The image of `R` is an `R`-order in `F`. -/
theorem isOrder_bot [Algebra R F] : IsOrder F (⊥ : Subalgebra R F) := by
  refine isOrder_iff.2 ⟨inferInstance, eq_top_iff.2 fun x _ => ?_⟩
  simpa using smul_mem (span F ((⊥ : Subalgebra R F) : Set F)) x
    (subset_span (one_mem (⊥ : Subalgebra R F)))

end Basic

section Commutative

variable {R F E : Type*} [CommRing R] [CommRing F] [CommRing E] [Algebra F E] [Algebra R E]

/-- In a commutative algebra, every `R`-order lies in the integral closure of `R`. -/
theorem IsOrder.le_integralClosure {Λ : Subalgebra R E} (h : IsOrder F Λ) :
    Λ ≤ integralClosure R E :=
  fun _ hx => h.isIntegral hx

end Commutative

section Lattice

variable {R F E : Type*} [CommRing R] [Field F] [Ring E]
  [Algebra R F] [IsFractionRing R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]

/-- Over a fraction field `F` of `R`, being an order is being a full `R`-lattice in `E`. -/
theorem isOrder_iff_isFullLattice {Λ : Subalgebra R E} :
    IsOrder F Λ ↔ (Subalgebra.toSubmodule Λ).IsFullLattice F :=
  ⟨fun h => { toIsLattice := IsLattice.of_fg F h.1, span_eq_top := h.2 },
    fun h => ⟨IsLattice.fg F _, h.span_eq_top⟩⟩

end Lattice

/-- The subring `ℚ ⊆ ℚ` spans `ℚ`, but it is not finitely generated over `ℤ`, so it is not an
order: `1 / 2` would be integral over `ℤ`, hence an integer. -/
theorem not_isOrder_top_rat : ¬IsOrder ℚ (⊤ : Subalgebra ℤ ℚ) := fun h => by
  obtain ⟨n, hn⟩ :=
    IsIntegrallyClosed.isIntegral_iff.1 (h.isIntegral (x := (1 / 2 : ℚ)) Algebra.mem_top)
  have hden := congrArg Rat.den hn
  rw [eq_intCast, Rat.den_intCast] at hden
  norm_num at hden

section Integral

variable {R F E : Type*} [CommRing R] [Field F] [Ring E]
  [Algebra R F] [IsFractionRing R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [FiniteDimensional F E]

/-- **Integral subalgebras lie in their own trace dual.** If every element of the `R`-subalgebra `Γ`
is integral over the integrally closed domain `R`, then the regular trace `Tr_F (x * y)` of a
product of two elements of `Γ` lies in `R`: `Γ` lies in its dual for the regular trace form. -/
theorem toSubmodule_le_dualSubmodule_regularTraceForm [IsIntegrallyClosed R] {Γ : Subalgebra R E}
    (hint : ∀ x ∈ Γ, IsIntegral R x) :
    Subalgebra.toSubmodule Γ ≤
      (Algebra.regularTraceForm F E).dualSubmodule (Subalgebra.toSubmodule Γ) := fun x hx y hy => by
  rw [Algebra.regularTraceForm_apply, mem_one]
  exact IsIntegrallyClosed.isIntegral_iff.1 <|
    Algebra.isIntegral_trace_lmul (K := F) (hint _ (Γ.mul_mem hx hy))

/-- **The trace-dual bound.** Let `R` be integrally closed and let `b` be an `F`-basis of `E` lying
in an `R`-subalgebra `Γ` of integral elements. Then `Γ` lies in the `R`-span of the basis dual to
`b` for the (nondegenerate) regular trace form. The bound depends only on `b`, so it holds
simultaneously for every such `Γ` containing `b`. -/
theorem toSubmodule_le_span_dualBasis [IsIntegrallyClosed R]
    (hB : (Algebra.regularTraceForm F E).Nondegenerate) {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι F E) {Γ : Subalgebra R E} (hb : ∀ i, b i ∈ Γ) (hint : ∀ x ∈ Γ, IsIntegral R x) :
    Subalgebra.toSubmodule Γ ≤
      span R (Set.range ((Algebra.regularTraceForm F E).dualBasis hB b)) := by
  rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis]
  exact (toSubmodule_le_dualSubmodule_regularTraceForm hint).trans <|
    (Algebra.regularTraceForm F E).dualSubmodule_anti (span_le.2 <| Set.range_subset_iff.2 hb)

/-- **Integral spanning subalgebras are orders.** Let `R` be an integrally closed noetherian domain
with fraction field `F`, and `E` a finite-dimensional `F`-algebra whose regular trace form
`(x, y) ↦ Tr_F (x * y)` is nondegenerate. An `R`-subalgebra of `E` spanning `E` over `F` and
consisting of elements integral over `R` is an `R`-order in `E`. -/
theorem isOrder_of_isIntegral [IsIntegrallyClosed R] [IsNoetherianRing R]
    (hB : (Algebra.regularTraceForm F E).Nondegenerate) {Λ : Subalgebra R E}
    (hint : ∀ x ∈ Λ, IsIntegral R x) (hspan : span F (Λ : Set E) = ⊤) : IsOrder F Λ := by
  classical
  -- `Λ` lies in the span of the trace dual basis of an `F`-basis of `E` made of elements of `Λ`
  let b := Basis.ofSpan hspan.ge
  have hle := toSubmodule_le_span_dualBasis hB b (fun i => Basis.ofSpan_subset _ ⟨i, rfl⟩) hint
  exact isOrder_iff.2 ⟨Module.Finite.iff_fg.2 ((fg_span (Set.finite_range _)).of_le hle), hspan⟩

/-- **Integral closures are orders.** The integral closure of an integrally closed noetherian domain
`R` in a finite separable extension `L` of its fraction field `F` is an `R`-order in `L`. -/
theorem integralClosure_isOrder [IsIntegrallyClosed R] [IsNoetherianRing R]
    (L : Type*) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] : IsOrder F (integralClosure R L) := by
  have := IsDomain.of_faithfulSMul R F
  exact isOrder_iff.2 ⟨IsIntegralClosure.finite R F L (integralClosure R L),
    span_integralClosure_eq_top⟩

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
  refine ⟨?_, eq_top_iff.2 ?_⟩
  · rw [toSubmodule_groupRingSubalgebra]
    exact fg_span (Set.finite_range _)
  · rw [← (MonoidAlgebra.basis G F).span_eq]
    exact span_mono <| Set.range_subset_iff.2 fun g => by
      simpa using single_one_mem_groupRingSubalgebra (R := R) g

end GroupRing

section Matrix

/-- The matrices with entries in a subalgebra `S` are the image of the matrices over `S` under
`S.val.mapMatrix`. -/
theorem _root_.Subalgebra.toSubmodule_matrix_eq_range_mapMatrix {R A n : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Fintype n] [DecidableEq n] (S : Subalgebra R A) :
    Subalgebra.toSubmodule (S.matrix : Subalgebra R (Matrix n n A)) =
      LinearMap.range (S.val.mapMatrix : Matrix n n S →ₐ[R] Matrix n n A).toLinearMap :=
  le_antisymm (fun M hM => ⟨fun i j => ⟨M i j, hM i j⟩, rfl⟩) <| by
    rintro _ ⟨N, rfl⟩ i j
    exact (N i j).property

variable {R F E : Type*} [CommRing R] [CommRing F] [Ring E] [Algebra F E] [Algebra R E]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- **Matrix orders.** If `Λ` is an `R`-order in `E`, then the matrices with entries in `Λ` form an
`R`-order in the matrix algebra `Matrix n n E`. For `Λ = R` in `E = F` this is the order `M_n(R)`
in `M_n(F)`. -/
theorem IsOrder.matrix {Λ : Subalgebra R E} (h : IsOrder F Λ) :
    IsOrder F (Λ.matrix : Subalgebra R (Matrix n n E)) := by
  have := h.finite
  refine ⟨?_, eq_top_iff.2 fun M _ => ?_⟩
  · -- the matrices over `Λ` are the image of the finite module `Matrix n n Λ = n → n → Λ`
    have : Module.Finite R (Matrix n n Λ) := inferInstanceAs (Module.Finite R (n → n → Λ))
    rw [Subalgebra.toSubmodule_matrix_eq_range_mapMatrix]
    exact Submodule.fg_range _
  -- every matrix is a sum of matrix units `single i j x` with `x` in the `F`-span of `Λ`
  rw [Matrix.matrix_eq_sum_single M]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have hx : M i j ∈ span F (Λ : Set E) := h.span_eq_top ▸ mem_top
  generalize M i j = x at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact subset_span (Matrix.single_mem_matrix Λ.zero_mem |>.2 hx)
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.single_add]; exact add_mem hx hy
  | smul c x _ hx => rw [← Matrix.smul_single]; exact smul_mem _ c hx

end Matrix

end TauCeti.IntegralOrder
