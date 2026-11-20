/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
-- Proof-only: torsion modules have rank zero.
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Linear maps between finitely generated abelian groups of equal rank

An injective `ℤ`-linear map `f : M → N` into a finitely generated abelian group of the same
rank has image of finite index `c`, so `c • y` lies in the image of `f` for every `y : N`.
Dividing by `f` gives a map `g : N → M` such that `f ∘ g` and `g ∘ f` are both multiplication by
`c`: an inverse of `f` up to a nonzero scalar. Over `ℚ` the map `f` becomes invertible with
inverse `c⁻¹ • g`; over `ℤ` an inverse up to a scalar is the best available.

The index of the image of a `ℤ`-linear map between free abelian groups is the absolute value of
the determinant of `f` in any bases of `M` and `N` indexed by the same finite type; a
non-injective `f` has image of infinite index (index `0`) and determinant `0`.

## Main results

* `LinearMap.exists_comp_eq_nsmul_id_of_injective`: an injective map between finitely generated
  abelian groups of equal rank has an inverse up to multiplication by a nonzero natural
  number.
* `LinearMap.index_range_eq_natAbs_det_toMatrix`: for any `ℤ`-linear map between free abelian
  groups with bases indexed by the same finite type, the index of the image is the absolute value
  of the determinant of its matrix.
* `Module.Basis.mem_span_range_nsmul_iff`, `Module.Basis.quotientSpanNSMulEquiv`: rescaling the
  vectors of a finite integral basis `b` by natural numbers `m k`, a vector lies in the span of the
  `m k • b k` exactly when its `k`-th coordinate is divisible by `m k`, and the quotient by that
  span is `Π k, ZMod (m k)`.
* `LinearIndependent.card_quotient_span_range_nsmul`: rescaling a finite linearly independent
  family `v` by natural numbers `m k` multiplies the order of the quotient by the span by
  `∏ k, m k`.
-/

public section

namespace LinearMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- An injective `ℤ`-linear map into a finitely generated abelian group of the same rank
has an inverse up to multiplication by a nonzero natural number `c`. -/
theorem exists_comp_eq_nsmul_id_of_injective [Module.Finite ℤ N] {f : M →ₗ[ℤ] N}
    (hf : Function.Injective f) (hrank : Module.finrank ℤ M = Module.finrank ℤ N) :
    ∃ c : ℕ, c ≠ 0 ∧ ∃ g : N →ₗ[ℤ] M, f ∘ₗ g = c • LinearMap.id ∧ g ∘ₗ f = c • LinearMap.id := by
  have : Finite (N ⧸ range f) := by
    have hq := (range f).finrank_quotient_add_finrank
    rw [(finrank_range_of_inj hf).trans hrank] at hq
    have hq0 : Module.finrank ℤ (N ⧸ range f) = 0 := by lia
    exact Module.finite_of_fg_torsion _ (Module.finrank_eq_zero_iff_isTorsion.mp hq0)
  have : Finite (N ⧸ (range f).toAddSubgroup) := ‹Finite (N ⧸ range f)›
  set c := (range f).toAddSubgroup.index
  let g : N →ₗ[ℤ] M := (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
    (c • LinearMap.id).codRestrict (range f) fun y ↦ (range f).toAddSubgroup.nsmul_index_mem y
  have hfg : f ∘ₗ g = c • LinearMap.id := by
    ext y
    simp [g]
  refine ⟨c, AddSubgroup.index_ne_zero_of_finite, g, hfg, ?_⟩
  ext x
  apply hf
  simpa using congr($hfg (f x))

/-- **The index of the image of a map is the absolute value of its determinant**: for bases `b` of
`M` and `c` of `N` indexed by the same finite type, the image of a `ℤ`-linear map `f : M → N` has
index `|det (toMatrix b c f)|`. A non-injective `f` has image of infinite index, hence index `0`,
and determinant `0`. -/
theorem index_range_eq_natAbs_det_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℤ N) (f : M →ₗ[ℤ] N) :
    (range f).toAddSubgroup.index = (toMatrix b c f).det.natAbs := by
  by_cases hf : Function.Injective f
  swap
  · -- a non-injective map has vanishing determinant and image of infinite index
    obtain ⟨v, hv, hv0⟩ := (ker f).ne_bot_iff.mp (mt ker_eq_bot.mp hf)
    have hdet : (toMatrix b c f).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun i ↦ b.repr v i, by simpa, ?_⟩
      simpa [toMatrix_mulVec_repr] using hv
    rw [hdet, Int.natAbs_zero, AddSubgroup.index_eq_zero_iff_infinite]
    refine not_finite_iff_infinite.mp fun h ↦ ?_
    have := Module.Finite.of_basis b
    have := Module.Finite.of_basis c
    have := Module.Free.of_basis c
    have := Module.Free.of_basis b
    have h1 := (Submodule.finiteQuotient_iff (range f)).mp h
    have h2 := (ker f).finrank_quotient_add_finrank
    rw [f.quotKerEquivRange.finrank_eq] at h2
    have h3 : 0 < Module.finrank ℤ (ker f) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, by simpa using hv0⟩
    rw [h1, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c] at h2
    lia
  rw [AddSubgroup.index_eq_natAbs_det c (range f).toAddSubgroup
    (b.map (LinearEquiv.ofInjective f hf)), Module.Basis.det_apply]
  congr 2
  ext i j
  simp only [toMatrix_apply, Module.Basis.toMatrix_apply, Module.Basis.map_apply]
  -- the `j`-th basis vector of the image is `f (b j)`, coerced through `AddSubgroup`
  exact congr(c.repr $(LinearEquiv.ofInjective_apply f (h := hf) (b j)) i)

end LinearMap

/-! ### Rescaled bases -/

namespace Module.Basis

variable {κ M : Type*} [AddCommGroup M] (b : Basis κ ℤ M) (m : κ → ℕ)

/-- A vector lies in the span of the rescaled basis vectors `m k • b k` exactly when, for every
`k`, its `k`-th coordinate in `b` is divisible by `m k`. -/
theorem mem_span_range_nsmul_iff [Finite κ] {x : M} :
    x ∈ Submodule.span ℤ (Set.range fun k ↦ m k • b k) ↔ ∀ k, (m k : ℤ) ∣ b.repr x k := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      intro k'
      rw [map_nsmul, b.repr_self, Finsupp.smul_apply]
      rcases eq_or_ne k k' with rfl | h
      · simp
      · simp [Finsupp.single_eq_of_ne' h]
    | zero => simp
    | add y z _ _ hy hz => exact fun k ↦ by simpa using dvd_add (hy k) (hz k)
    | smul a y _ hy => exact fun k ↦ by simpa using (hy k).mul_left a
  · intro h
    choose q hq using h
    have := Fintype.ofFinite κ
    rw [← b.sum_repr x]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [hq k, mul_comm, mul_smul, natCast_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The coordinates in `b`, the `k`-th one reduced modulo `m k`. -/
private noncomputable def coordModNSMul : M →ₗ[ℤ] (k : κ) → ZMod (m k) :=
  LinearMap.pi fun k ↦ (Int.castAddHom (ZMod (m k))).toIntLinearMap ∘ₗ b.coord k

private theorem coordModNSMul_apply (x : M) (k : κ) :
    coordModNSMul b m x k = (b.repr x k : ZMod (m k)) :=
  (rfl)

private theorem ker_coordModNSMul [Finite κ] :
    LinearMap.ker (coordModNSMul b m) = Submodule.span ℤ (Set.range fun k ↦ m k • b k) := by
  ext x
  simp [mem_span_range_nsmul_iff, funext_iff, coordModNSMul_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

private theorem coordModNSMul_surjective [Finite κ] : Function.Surjective (coordModNSMul b m) := by
  classical
  have := Fintype.ofFinite κ
  intro y
  refine ⟨∑ k, ((y k).cast : ℤ) • b k, funext fun k ↦ ?_⟩
  simp [coordModNSMul_apply, Finsupp.single_apply]

/-- **The quotient by a rescaled basis.** Reducing the `k`-th coordinate in `b` modulo `m k`
identifies the quotient of `M` by the span of the vectors `m k • b k` with `Π k, ZMod (m k)`. -/
noncomputable def quotientSpanNSMulEquiv [Finite κ] :
    (M ⧸ Submodule.span ℤ (Set.range fun k ↦ m k • b k)) ≃ₗ[ℤ] ((k : κ) → ZMod (m k)) :=
  (Submodule.quotEquivOfEq _ _ (ker_coordModNSMul b m).symm).trans
    ((coordModNSMul b m).quotKerEquivOfSurjective (coordModNSMul_surjective b m))

@[simp]
theorem quotientSpanNSMulEquiv_mk [Finite κ] (x : M) (k : κ) :
    b.quotientSpanNSMulEquiv m (Submodule.Quotient.mk x) k = (b.repr x k : ZMod (m k)) :=
  (rfl)

/-- The quotient of `M` by the span of the rescaled basis vectors `m k • b k` has `∏ k, m k`
elements; it is infinite, of cardinality `0` in `Nat.card`, when some `m k` vanishes. -/
theorem card_quotient_span_range_nsmul [Fintype κ] :
    Nat.card (M ⧸ Submodule.span ℤ (Set.range fun k ↦ m k • b k)) = ∏ k, m k := by
  simp [Nat.card_congr (b.quotientSpanNSMulEquiv m).toEquiv, Nat.card_pi]

end Module.Basis

/-- **Rescaling a linearly independent family.** Rescaling a finite linearly independent family
`v` in an abelian group by natural numbers `m k` multiplies the order of the quotient by its span
by `∏ k, m k`. Both sides are `0` when one of the quotients is infinite. -/
theorem LinearIndependent.card_quotient_span_range_nsmul {κ M : Type*} [AddCommGroup M]
    [Fintype κ] {v : κ → M} (hv : LinearIndependent ℤ v) (m : κ → ℕ) :
    Nat.card (M ⧸ Submodule.span ℤ (Set.range fun k ↦ m k • v k)) =
      (∏ k, m k) * Nat.card (M ⧸ Submodule.span ℤ (Set.range v)) := by
  set Q := Submodule.span ℤ (Set.range v)
  set P := Submodule.span ℤ (Set.range fun k ↦ m k • v k)
  have hPQ : P ≤ Q := Submodule.span_le.2 <| by
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  -- In the basis `b` of `Q` given by `v`, `P` is the span of the rescaled basis vectors.
  let b := Module.Basis.span hv
  have hcomap : P.comap Q.subtype = Submodule.span ℤ (Set.range fun k ↦ m k • b k) := by
    rw [← Submodule.comap_map_eq_of_injective Q.injective_subtype
      (Submodule.span ℤ (Set.range fun k ↦ m k • b k)), Submodule.map_span, ← Set.range_comp]
    have hb : (Q.subtype ∘ fun k ↦ m k • b k) = fun k ↦ m k • v k := by
      ext k
      simp [b, Module.Basis.span_apply]
    rw [hb]
  -- The quotient of `Q` by `P` is the image of `Q` in `M ⧸ P`, by the first isomorphism theorem.
  have hker : LinearMap.ker (P.mkQ ∘ₗ Q.subtype) = P.comap Q.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (P.mkQ ∘ₗ Q.subtype) = Q.map P.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← Submodule.card_quotient_mul_card_quotient Q P hPQ, ← b.card_quotient_span_range_nsmul m,
    ← hcomap]
  congr 1
  exact Nat.card_congr ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((P.mkQ ∘ₗ Q.subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))).toEquiv.symm
