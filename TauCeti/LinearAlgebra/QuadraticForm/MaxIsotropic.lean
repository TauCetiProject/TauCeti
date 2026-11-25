/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
import Mathlib.Algebra.Field.ZMod
import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Maximal isotropic subspaces of a quadratic space

A submodule `W` of a quadratic module `(M, Q)` is *maximal isotropic* when `Q` vanishes on `W`
and `W` is its own orthogonal complement for the polar bilinear form `b_Q`. The quadratic module
is *weakly metabolic* when `b_Q` is nondegenerate and a maximal isotropic submodule exists.

These are the parameter spaces of Poonen and Rains' random model for Selmer groups: for a weakly
metabolic quadratic space of dimension `2n` over a finite field, the dimension of the
intersection of a fixed and a uniformly random maximal isotropic subspace has an explicit law.
The definitions work in every characteristic. In characteristic two the vanishing of `Q` on `W`
is part of the definition: polar self-orthogonality alone does not imply it
(`TauCeti.orthogonal_polarBilin_span_eq_self_binaryQuadraticForm_zero`), whereas when `2` is
invertible it does (`QuadraticMap.isMaxIsotropic_iff_orthogonal_polarBilin_eq`).

## Main definitions

* `QuadraticMap.IsMaxIsotropic`: a submodule on which `Q` vanishes and which equals its polar
  orthogonal complement.
* `QuadraticMap.maxIsotropicSubspaces`: the set of maximal isotropic submodules.
* `QuadraticMap.IsWeaklyMetabolic`: the polar form is nondegenerate and a maximal isotropic
  submodule exists.
* `QuadraticMap.IsometryEquiv.maxIsotropicSubspacesEquiv`: an isometric equivalence induces a
  bijection between the sets of maximal isotropic submodules.

## Main results

* `QuadraticMap.IsMaxIsotropic.maximal`: a maximal isotropic submodule is maximal among totally
  isotropic submodules.
* `QuadraticMap.isMaxIsotropic_iff_two_mul_finrank_eq`: in a finite-dimensional quadratic space
  with trivial radical, a submodule is maximal isotropic exactly when `Q` vanishes on it and it
  has half the ambient dimension.
* `QuadraticMap.IsWeaklyMetabolic.finrank_eq`: in a weakly metabolic space of dimension `2n`,
  every maximal isotropic subspace has dimension `n`.
* `QuadraticMap.maxIsotropicSubspaces_eq_singleton_bot`: on the zero module the zero submodule is
  the unique maximal isotropic submodule.
* `TauCeti.maxIsotropicSubspaces_binaryQuadraticForm_zero`: for `Q(x, y) = xy` on `R²` over
  an integral domain the maximal isotropic submodules are exactly the two coordinate axes.
* `QuadraticMap.isWeaklyMetabolic_iff_equivalent_binaryQuadraticForm_zero`: a two-dimensional
  quadratic space is weakly metabolic exactly when it is isometric to `(K², xy)`.
* `QuadraticMap.IsWeaklyMetabolic.ncard_maxIsotropicSubspaces_of_finrank_eq_two`: a weakly
  metabolic plane has exactly two maximal isotropic lines.

## References

* B. Poonen and E. Rains, *Random maximal isotropic subspaces and Selmer groups*,
  J. Amer. Math. Soc. 25 (2012), §2.1.
-/

public section

open Module

namespace QuadraticMap

open TauCeti

section CommRing

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] {Q : QuadraticForm R M} {Q' : QuadraticForm R M'} {W W' : Submodule R M}

/-- A submodule `W` is *maximal isotropic* for a quadratic form `Q` when `Q` vanishes on `W` and
`W` equals its orthogonal complement for the polar bilinear form of `Q`. -/
def IsMaxIsotropic (Q : QuadraticForm R M) (W : Submodule R M) : Prop :=
  Q.IsTotallyIsotropic W ∧ LinearMap.BilinForm.orthogonal Q.polarBilin W = W

/-- Unfolds `QuadraticMap.IsMaxIsotropic`. -/
theorem isMaxIsotropic_iff :
    Q.IsMaxIsotropic W ↔
      Q.IsTotallyIsotropic W ∧ LinearMap.BilinForm.orthogonal Q.polarBilin W = W :=
  Iff.rfl

/-- A maximal isotropic submodule is totally isotropic. -/
theorem IsMaxIsotropic.isTotallyIsotropic (hW : Q.IsMaxIsotropic W) : Q.IsTotallyIsotropic W :=
  hW.1

/-- A maximal isotropic submodule equals its polar orthogonal complement. -/
theorem IsMaxIsotropic.orthogonal_polarBilin_eq (hW : Q.IsMaxIsotropic W) :
    LinearMap.BilinForm.orthogonal Q.polarBilin W = W :=
  hW.2

/-- A vector lies in a maximal isotropic submodule `W` exactly when it is polar-orthogonal to
every vector of `W`. -/
theorem IsMaxIsotropic.mem_iff_forall_polar_eq_zero (hW : Q.IsMaxIsotropic W) {v : M} :
    v ∈ W ↔ ∀ w ∈ W, polar Q w v = 0 := by
  conv_lhs => rw [← hW.orthogonal_polarBilin_eq]
  simp [LinearMap.BilinForm.mem_orthogonal_iff]

/-- A maximal isotropic submodule contained in a submodule with the same orthogonality property
is equal to it. -/
theorem IsMaxIsotropic.eq_of_le (hW : Q.IsMaxIsotropic W)
    (hW' : LinearMap.BilinForm.orthogonal Q.polarBilin W' = W') (h : W ≤ W') : W = W' := by
  refine le_antisymm h ?_
  rw [← hW', ← hW.orthogonal_polarBilin_eq]
  exact LinearMap.BilinForm.orthogonal_le h

/-- A maximal isotropic submodule is maximal among the totally isotropic submodules: a totally
isotropic `U ≥ W` satisfies `U ≤ U^⊥ ≤ W^⊥ = W`. -/
theorem IsMaxIsotropic.maximal (hW : Q.IsMaxIsotropic W) : Maximal Q.IsTotallyIsotropic W := by
  refine ⟨hW.isTotallyIsotropic, fun U hU hle ↦ ?_⟩
  calc U ≤ LinearMap.BilinForm.orthogonal Q.polarBilin U := hU.le_orthogonal_polarBilin
    _ ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W := LinearMap.BilinForm.orthogonal_le hle
    _ = W := hW.orthogonal_polarBilin_eq

/-- When `2` is invertible, a submodule is maximal isotropic exactly when it equals its polar
orthogonal complement: polar self-orthogonality already forces `Q` to vanish on it. -/
theorem isMaxIsotropic_iff_orthogonal_polarBilin_eq [Invertible (2 : R)] :
    Q.IsMaxIsotropic W ↔ LinearMap.BilinForm.orthogonal Q.polarBilin W = W := by
  refine ⟨IsMaxIsotropic.orthogonal_polarBilin_eq,
    fun h ↦ ⟨isTotallyIsotropic_iff.mpr fun v hv ↦ ?_, h⟩⟩
  have hv' : v ∈ LinearMap.BilinForm.orthogonal Q.polarBilin W := h.symm ▸ hv
  have hpolar : polar Q v v = 0 := LinearMap.BilinForm.mem_orthogonal_iff.mp hv' v hv
  rw [polar_self, two_nsmul, ← two_mul] at hpolar
  rw [← invOf_mul_cancel_left (2 : R) (Q v), hpolar, mul_zero]

/-- The set of maximal isotropic submodules of a quadratic form. -/
def maxIsotropicSubspaces (Q : QuadraticForm R M) : Set (Submodule R M) :=
  {W | Q.IsMaxIsotropic W}

/-- Membership in `QuadraticMap.maxIsotropicSubspaces` is being maximal isotropic. -/
@[simp]
theorem mem_maxIsotropicSubspaces : W ∈ Q.maxIsotropicSubspaces ↔ Q.IsMaxIsotropic W :=
  Iff.rfl

/-- A quadratic form is *weakly metabolic* when its polar bilinear form is nondegenerate and it
has a maximal isotropic submodule. -/
def IsWeaklyMetabolic (Q : QuadraticForm R M) : Prop :=
  Q.polarBilin.Nondegenerate ∧ Q.maxIsotropicSubspaces.Nonempty

/-- Unfolds `QuadraticMap.IsWeaklyMetabolic`. -/
theorem isWeaklyMetabolic_iff :
    Q.IsWeaklyMetabolic ↔ Q.polarBilin.Nondegenerate ∧ ∃ W, Q.IsMaxIsotropic W :=
  Iff.rfl

/-- The polar bilinear form of a weakly metabolic quadratic form is nondegenerate. -/
theorem IsWeaklyMetabolic.nondegenerate_polarBilin (hQ : Q.IsWeaklyMetabolic) :
    Q.polarBilin.Nondegenerate :=
  hQ.1

/-- A weakly metabolic quadratic form has a maximal isotropic submodule. -/
theorem IsWeaklyMetabolic.exists_isMaxIsotropic (hQ : Q.IsWeaklyMetabolic) :
    ∃ W, Q.IsMaxIsotropic W :=
  hQ.2

/-- A weakly metabolic quadratic form has trivial radical. -/
theorem IsWeaklyMetabolic.radical_eq_bot (hQ : Q.IsWeaklyMetabolic) : Q.radical = ⊥ :=
  (nondegenerate_of_nondegenerate_polarBilin hQ.nondegenerate_polarBilin).radical_eq_bot

/-! ### Degenerate cases -/

/-- The zero submodule is maximal isotropic exactly when the module is zero. -/
@[simp]
theorem isMaxIsotropic_bot_iff : Q.IsMaxIsotropic ⊥ ↔ Subsingleton M := by
  rw [isMaxIsotropic_iff, LinearMap.BilinForm.orthogonal_bot, eq_comm,
    ← Submodule.subsingleton_iff R, subsingleton_iff_bot_eq_top]
  exact and_iff_right isTotallyIsotropic_bot

/-- On the zero module the zero submodule is the unique maximal isotropic submodule. -/
theorem maxIsotropicSubspaces_eq_singleton_bot [Subsingleton M] :
    Q.maxIsotropicSubspaces = {⊥} := by
  ext W
  rw [Subsingleton.elim W ⊥]
  simpa using ‹Subsingleton M›

/-- Every quadratic form on the zero module is weakly metabolic. -/
theorem isWeaklyMetabolic_of_subsingleton [Subsingleton M] : Q.IsWeaklyMetabolic :=
  ⟨⟨fun x _ ↦ Subsingleton.elim x 0, fun x _ ↦ Subsingleton.elim x 0⟩,
    ⟨⊥, isMaxIsotropic_bot_iff.mpr ‹_›⟩⟩

/-- An anisotropic quadratic form on a nonzero module has no maximal isotropic submodule. -/
theorem maxIsotropicSubspaces_eq_empty_of_anisotropic [Nontrivial M] (hQ : Q.Anisotropic) :
    Q.maxIsotropicSubspaces = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun W hW ↦ ?_
  have hbot : W = ⊥ := (Submodule.eq_bot_iff W).mpr fun v hv ↦
    hQ v (hW.isTotallyIsotropic.apply_eq_zero hv)
  rw [mem_maxIsotropicSubspaces, hbot, isMaxIsotropic_bot_iff] at hW
  exact not_subsingleton M hW

/-- An anisotropic quadratic form on a nonzero module is not weakly metabolic. -/
theorem IsWeaklyMetabolic.not_anisotropic [Nontrivial M] (hQ : Q.IsWeaklyMetabolic) :
    ¬Q.Anisotropic := fun h ↦ by
  simpa [maxIsotropicSubspaces_eq_empty_of_anisotropic h] using hQ.2

/-! ### Transport along isometries -/

/-- An isometric equivalence carries maximal isotropic submodules to maximal isotropic
submodules. -/
@[simp]
theorem IsometryEquiv.isMaxIsotropic_map_iff (e : Q.IsometryEquiv Q') :
    Q'.IsMaxIsotropic (W.map e.toLinearMap) ↔ Q.IsMaxIsotropic W := by
  have hcomp : Q'.comp e.toLinearMap = Q := QuadraticMap.ext e.map_app
  have hTI : Q'.IsTotallyIsotropic (W.map e.toLinearMap) ↔ Q.IsTotallyIsotropic W := by
    rw [← isTotallyIsotropic_comp_iff, hcomp]
  rw [isMaxIsotropic_iff, isMaxIsotropic_iff, hTI, ← e.map_orthogonal_polarBilin,
    (Submodule.map_injective_of_injective e.toLinearEquiv.injective).eq_iff]

/-- An isometric equivalence induces a bijection between the sets of maximal isotropic
submodules, sending `W` to its image. -/
def IsometryEquiv.maxIsotropicSubspacesEquiv (e : Q.IsometryEquiv Q') :
    Q.maxIsotropicSubspaces ≃ Q'.maxIsotropicSubspaces :=
  (Submodule.orderIsoMapComap e.toLinearEquiv).toEquiv.subtypeEquiv fun _ ↦
    e.isMaxIsotropic_map_iff.symm

/-- The bijection induced by an isometric equivalence sends a maximal isotropic submodule to its
image. -/
@[simp]
theorem IsometryEquiv.coe_maxIsotropicSubspacesEquiv_apply (e : Q.IsometryEquiv Q')
    (W : Q.maxIsotropicSubspaces) :
    (e.maxIsotropicSubspacesEquiv W : Submodule R M') =
      (W : Submodule R M).map e.toLinearMap :=
  (rfl)

/-- The inverse of the bijection induced by an isometric equivalence sends a maximal isotropic
submodule to its image under the inverse isometry. -/
@[simp]
theorem IsometryEquiv.coe_maxIsotropicSubspacesEquiv_symm_apply (e : Q.IsometryEquiv Q')
    (W : Q'.maxIsotropicSubspaces) :
    (e.maxIsotropicSubspacesEquiv.symm W : Submodule R M) =
      (W : Submodule R M').map e.symm.toLinearMap :=
  Submodule.orderIsoMapComap_symm_apply' e.toLinearEquiv W

/-- Isometric quadratic forms have the same number of maximal isotropic submodules. -/
theorem IsometryEquiv.ncard_maxIsotropicSubspaces_eq (e : Q.IsometryEquiv Q') :
    Q.maxIsotropicSubspaces.ncard = Q'.maxIsotropicSubspaces.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr e.maxIsotropicSubspacesEquiv]

/-- Weak metabolicity is invariant under isometric equivalence. -/
theorem IsometryEquiv.isWeaklyMetabolic_iff (e : Q.IsometryEquiv Q') :
    Q.IsWeaklyMetabolic ↔ Q'.IsWeaklyMetabolic := by
  rw [IsWeaklyMetabolic, IsWeaklyMetabolic, e.nondegenerate_polarBilin_iff,
    ← Set.nonempty_coe_sort, ← Set.nonempty_coe_sort,
    e.maxIsotropicSubspacesEquiv.nonempty_congr]

/-- Weak metabolicity is invariant under isometry. -/
theorem Equivalent.isWeaklyMetabolic_iff (h : Q.Equivalent Q') :
    Q.IsWeaklyMetabolic ↔ Q'.IsWeaklyMetabolic :=
  h.some.isWeaklyMetabolic_iff

end CommRing

end QuadraticMap

open QuadraticMap

namespace TauCeti

/-! ### The hyperbolic plane `xy` -/

section CommRing

variable {R : Type*} [CommRing R]

/-- Each coordinate axis is its own polar orthogonal complement for `xy`. -/
private theorem orthogonal_polarBilin_ker_proj (i : Fin 2) :
    LinearMap.BilinForm.orthogonal (binaryQuadraticForm R 0 0).polarBilin
        (LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) i)) =
      LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) i) := by
  ext y
  simp only [LinearMap.BilinForm.mem_orthogonal_iff,
    polarBilin_apply_apply, polar_binaryQuadraticForm_zero, LinearMap.mem_ker,
    LinearMap.proj_apply]
  refine ⟨fun h ↦ ?_, fun h x hx ↦ ?_⟩
  · have := h (Pi.single i.rev 1) (by fin_cases i <;> simp)
    fin_cases i <;> simpa using this
  · fin_cases i <;> simp_all

/-- Each coordinate axis is maximal isotropic for `xy`. -/
theorem isMaxIsotropic_ker_proj_binaryQuadraticForm_zero (i : Fin 2) :
    (binaryQuadraticForm R 0 0).IsMaxIsotropic
      (LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) i)) :=
  ⟨isTotallyIsotropic_iff.mpr fun x hx ↦ by fin_cases i <;> simp_all [binaryQuadraticForm_apply],
    orthogonal_polarBilin_ker_proj i⟩

/-- The hyperbolic plane `xy` is weakly metabolic over every commutative ring. -/
theorem isWeaklyMetabolic_binaryQuadraticForm_zero :
    (binaryQuadraticForm R 0 0).IsWeaklyMetabolic :=
  ⟨nondegenerate_polarBilin_binaryQuadraticForm_zero,
    ⟨_, isMaxIsotropic_ker_proj_binaryQuadraticForm_zero 1⟩⟩

/-- A submodule on which `xy` vanishes lies in one of the two coordinate axes. -/
private theorem le_ker_proj_or_le_ker_proj_of_isTotallyIsotropic [IsDomain R]
    {W : Submodule R (Fin 2 → R)} (hW : (binaryQuadraticForm R 0 0).IsTotallyIsotropic W) :
    W ≤ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 1) ∨
      W ≤ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 0) := by
  have hQ : ∀ v ∈ W, v 0 * v 1 = 0 := fun v hv ↦ by
    simpa [binaryQuadraticForm_apply] using hW.apply_eq_zero hv
  by_contra! h
  obtain ⟨⟨a, ha, ha1⟩, ⟨b, hb, hb0⟩⟩ := And.intro (IsConcreteLE.not_le_iff_exists.mp h.1)
    (IsConcreteLE.not_le_iff_exists.mp h.2)
  simp only [LinearMap.mem_ker, LinearMap.proj_apply] at ha1 hb0
  have ha0 : a 0 = 0 := (mul_eq_zero.mp (hQ a ha)).resolve_right ha1
  have hb1 : b 1 = 0 := (mul_eq_zero.mp (hQ b hb)).resolve_left hb0
  have hab := hQ (a + b) (W.add_mem ha hb)
  simp only [Pi.add_apply, ha0, hb1, zero_add, add_zero] at hab
  exact mul_ne_zero hb0 ha1 hab

/-- Over an integral domain, the maximal isotropic submodules of the hyperbolic plane `xy` are
exactly the two coordinate axes. -/
theorem isMaxIsotropic_binaryQuadraticForm_zero_iff [IsDomain R] {W : Submodule R (Fin 2 → R)} :
    (binaryQuadraticForm R 0 0).IsMaxIsotropic W ↔
      W = LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 1) ∨
        W = LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 0) := by
  refine ⟨fun hW ↦ ?_, ?_⟩
  · exact (le_ker_proj_or_le_ker_proj_of_isTotallyIsotropic hW.isTotallyIsotropic).imp
      (hW.eq_of_le (orthogonal_polarBilin_ker_proj 1))
      (hW.eq_of_le (orthogonal_polarBilin_ker_proj 0))
  · rintro (rfl | rfl) <;> exact isMaxIsotropic_ker_proj_binaryQuadraticForm_zero _

/-- Over an integral domain, the maximal isotropic submodules of the hyperbolic plane `xy` are
exactly the two coordinate axes. -/
theorem maxIsotropicSubspaces_binaryQuadraticForm_zero [IsDomain R] :
    (binaryQuadraticForm R 0 0).maxIsotropicSubspaces =
      {LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 1),
        LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 0)} := by
  ext W
  simp [isMaxIsotropic_binaryQuadraticForm_zero_iff]

/-- Over an integral domain, the hyperbolic plane `xy` has exactly two maximal isotropic
submodules. -/
theorem ncard_maxIsotropicSubspaces_binaryQuadraticForm_zero [IsDomain R] :
    (binaryQuadraticForm R 0 0).maxIsotropicSubspaces.ncard = 2 := by
  rw [maxIsotropicSubspaces_binaryQuadraticForm_zero, Set.ncard_pair]
  intro h
  have : (Pi.single 0 1 : Fin 2 → R) ∈
      LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 0) := h ▸ by simp
  simp at this

/-- When `2 = 0`, the diagonal line of the hyperbolic plane `xy` is its own polar orthogonal
complement. -/
theorem orthogonal_polarBilin_span_eq_self_binaryQuadraticForm_zero (h2 : (2 : R) = 0) :
    LinearMap.BilinForm.orthogonal (binaryQuadraticForm R 0 0).polarBilin (R ∙ ![1, 1]) =
      R ∙ ![1, 1] := by
  have hneg : ∀ r : R, -r = r := fun r ↦ by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
  ext y
  simp only [LinearMap.BilinForm.mem_orthogonal_iff,
    Submodule.mem_span_singleton, forall_exists_index, forall_apply_eq_imp_iff,
    polarBilin_apply_apply, polar_binaryQuadraticForm_zero]
  refine ⟨fun hy ↦ ⟨y 0, ?_⟩, ?_⟩
  · have h := hy 1
    simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
      one_mul] at h
    have hy1 : y 1 = y 0 := by rw [← hneg (y 0)]; exact eq_neg_of_add_eq_zero_left h
    ext i
    fin_cases i <;> simp [hy1]
  · rintro ⟨c, rfl⟩ a
    simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, mul_one]
    rw [← two_mul, h2, zero_mul]

/-- Over a nonzero ring, the diagonal line of the hyperbolic plane `xy` is not maximal isotropic,
since `xy` takes the value `1` at `(1, 1)`. When `2 = 0` this line is nevertheless its own polar
orthogonal complement (`TauCeti.orthogonal_polarBilin_span_eq_self_binaryQuadraticForm_zero`),
so polar self-orthogonality does not imply maximal isotropy in characteristic two. -/
theorem not_isMaxIsotropic_span_binaryQuadraticForm_zero [Nontrivial R] :
    ¬(binaryQuadraticForm R 0 0).IsMaxIsotropic (R ∙ ![1, 1]) := fun h ↦ by
  simpa [binaryQuadraticForm_apply] using
    h.isTotallyIsotropic.apply_eq_zero (Submodule.mem_span_singleton_self _)

end CommRing

/-- The form `x² + xy + y²` on `𝔽₂²` is anisotropic, so it is not weakly metabolic, although its
polar form is nondegenerate
(`TauCeti.nondegenerate_polarBilin_binaryQuadraticForm_of_two_mul_eq_zero`). -/
theorem not_isWeaklyMetabolic_binaryQuadraticForm_zmod_two_one_one :
    ¬(binaryQuadraticForm (ZMod 2) 1 1).IsWeaklyMetabolic := fun h ↦
  h.not_anisotropic <| (anisotropic_binaryQuadraticForm_one_iff (1 : ZMod 2)).mpr <| by decide

end TauCeti

namespace QuadraticMap

open TauCeti

/-! ### Dimension theory over a field -/

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {W : Submodule K V}

/-- In a finite-dimensional quadratic space with trivial radical, a submodule is maximal isotropic
exactly when `Q` vanishes on it and it has half the ambient dimension. -/
theorem isMaxIsotropic_iff_two_mul_finrank_eq [FiniteDimensional K V] (hQ : Q.radical = ⊥) :
    Q.IsMaxIsotropic W ↔ Q.IsTotallyIsotropic W ∧ 2 * finrank K W = finrank K V :=
  and_congr_right fun hW ↦ hW.orthogonal_polarBilin_eq_self_iff hQ

/-- In a finite-dimensional quadratic space with trivial radical, a maximal isotropic subspace has
half the ambient dimension. -/
theorem IsMaxIsotropic.two_mul_finrank_eq [FiniteDimensional K V] (hQ : Q.radical = ⊥)
    (hW : Q.IsMaxIsotropic W) : 2 * finrank K W = finrank K V :=
  ((isMaxIsotropic_iff_two_mul_finrank_eq hQ).mp hW).2

/-- In a quadratic space of dimension `2n` with trivial radical, a totally isotropic subspace of
dimension `n` is maximal isotropic. -/
theorem IsTotallyIsotropic.isMaxIsotropic_of_finrank_eq [FiniteDimensional K V]
    (hQ : Q.radical = ⊥) (hW : Q.IsTotallyIsotropic W) {n : ℕ} (hV : finrank K V = 2 * n)
    (hWn : finrank K W = n) : Q.IsMaxIsotropic W :=
  (isMaxIsotropic_iff_two_mul_finrank_eq hQ).mpr ⟨hW, by omega⟩

/-- A finite-dimensional weakly metabolic quadratic space has even dimension. -/
theorem IsWeaklyMetabolic.even_finrank [FiniteDimensional K V] (hQ : Q.IsWeaklyMetabolic) :
    Even (finrank K V) := by
  obtain ⟨W, hW⟩ := hQ.exists_isMaxIsotropic
  exact ⟨finrank K W, by rw [← hW.two_mul_finrank_eq hQ.radical_eq_bot]; ring⟩

/-- In a weakly metabolic quadratic space of dimension `2n`, every maximal isotropic subspace has
dimension `n`. -/
theorem IsWeaklyMetabolic.finrank_eq [FiniteDimensional K V] (hQ : Q.IsWeaklyMetabolic) {n : ℕ}
    (hV : finrank K V = 2 * n) (hW : Q.IsMaxIsotropic W) : finrank K W = n := by
  have := hW.two_mul_finrank_eq hQ.radical_eq_bot
  omega

/-! ### Weakly metabolic planes -/

/-- A weakly metabolic plane is isometric to the hyperbolic plane `(K², xy)`. -/
theorem IsWeaklyMetabolic.equivalent_binaryQuadraticForm_zero (hQ : Q.IsWeaklyMetabolic)
    (hV : finrank K V = 2) : Q.Equivalent (binaryQuadraticForm K 0 0) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  obtain ⟨W, hW⟩ := hQ.exists_isMaxIsotropic
  have hW1 : finrank K W = 1 := hQ.finrank_eq (n := 1) hV hW
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show W ≠ ⊥ by
    rintro rfl
    simp at hW1)
  have hw := hW.isTotallyIsotropic.apply_eq_zero hwW
  obtain ⟨f, hf, hwf⟩ := exists_isotropic_polar_eq_one_of_radical_eq_bot hQ.radical_eq_bot hw0 hw
  exact Q.equivalent_binaryQuadraticForm_zero_of_polar_eq_one hV hw hf hwf

/-- A two-dimensional quadratic space is weakly metabolic exactly when it is isometric to the
hyperbolic plane `(K², xy)`. -/
theorem isWeaklyMetabolic_iff_equivalent_binaryQuadraticForm_zero (hV : finrank K V = 2) :
    Q.IsWeaklyMetabolic ↔ Q.Equivalent (binaryQuadraticForm K 0 0) :=
  ⟨fun hQ ↦ hQ.equivalent_binaryQuadraticForm_zero hV, fun h ↦
    h.isWeaklyMetabolic_iff.mpr isWeaklyMetabolic_binaryQuadraticForm_zero⟩

/-- A weakly metabolic plane has exactly two maximal isotropic lines. -/
theorem IsWeaklyMetabolic.ncard_maxIsotropicSubspaces_of_finrank_eq_two
    (hQ : Q.IsWeaklyMetabolic) (hV : finrank K V = 2) : Q.maxIsotropicSubspaces.ncard = 2 := by
  rw [(hQ.equivalent_binaryQuadraticForm_zero hV).some.ncard_maxIsotropicSubspaces_eq,
    ncard_maxIsotropicSubspaces_binaryQuadraticForm_zero]

end Field

end QuadraticMap
