/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Subring
-- Proof-only: the endomorphisms of an ordinary curve commute.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ordinary
-- Proof-only: `π̂ = a_q - π`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Charpoly
-- Proof-only: the dual is additive, and `f̂ + f` is an integer.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Degree

/-!
# The endomorphism ring of an ordinary elliptic curve over a finite field

Let `W` be an ordinary elliptic curve over a finite field `F` with `q` elements, `π` its Frobenius
endomorphism and `a = a_q` its trace of Frobenius. This file proves that the endomorphism ring
`Hom W W` is a free `ℤ`-module of rank `2` containing the subring `ℤ[π] = ℤ + ℤπ` with finite
index: a fixed nonzero integer `N` multiplies every endomorphism into `ℤ[π]`. Since `Hom W W` is
moreover commutative (`WeierstrassCurve.mul_comm_of_isOrdinary`), it is an order in the imaginary
quadratic field `ℚ(π)` containing `ℤ[π]` (Silverman V.3.1 and III.9.4). The inclusion of `ℤ[π]`
can be strict: on `y² = x³ + x` over `𝔽₅` the index is `2`.

The proof uses the dual. Every endomorphism `f` has an integer trace `t`, with `f + f̂ = t`, so
`u = 2f - t` is anti-self-dual, `û = -u`, and therefore `u² = -u û = -deg u` is an integer. The
same holds for `v = 2π - a`, which is nonzero because `1` and `π` are linearly independent on an
ordinary curve. As `u + v` is anti-self-dual as well, `(u + v)² = u² + 2uv + v²` shows that `2uv`
is an integer `e`, using that `u` and `v` commute. Multiplying by `v` gives
`2 deg v • u = -e • v`, hence `4 deg v • f = 2 deg v t - e v ∈ ℤ[π]`. So `N = 4 deg v` works, and
`f ↦ N • f` embeds `Hom W W` into `ℤ[π]`, which has rank `2`.

## Main results

* `WeierstrassCurve.exists_zsmul_mem_adjoin_ofIsogeny_frobeniusIsogeny_of_isOrdinary`: a fixed
  nonzero integer multiplies every endomorphism of an ordinary curve into `ℤ[π]`.
* `WeierstrassCurve.module_finite_hom_of_isOrdinary` and
  `WeierstrassCurve.finrank_hom_of_isOrdinary`: the endomorphism ring of an ordinary curve is a
  finitely generated `ℤ`-module of rank `2`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.2, III.9.4, V.2.3.1
  and V.3.1.
-/

public section

open TauCeti.Isogeny

namespace WeierstrassCurve

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic]

/-- An anti-self-dual endomorphism squares to minus its degree. -/
private theorem mul_self_eq_neg_degree {x : Hom W.toAffine W.toAffine} (hx : x.dual = -x) :
    x * x = -((x.degree : ℤ) • 1) := by
  have h := x.comp_dual_self
  rw [hx, Hom.comp_neg, ← Hom.mul_def, ← Hom.one_def, ← natCast_zsmul] at h
  rw [← h, neg_neg]

variable [Finite F] {p : ℕ} [ExpChar F p]

/-- **A fixed nonzero integer multiplies the endomorphism ring of an ordinary curve into `ℤ[π]`**
(Silverman V.3.1, III.9.4). So `ℤ[π]` has finite index in the endomorphism ring, which therefore
lies in `ℚ(π)`. The integer `N = 4 deg (2π - a_q) = 4 (4q - a_q²)` works. -/
theorem exists_zsmul_mem_adjoin_ofIsogeny_frobeniusIsogeny_of_isOrdinary (hW : W.IsOrdinary p) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ f : Hom W.toAffine W.toAffine,
      N • f ∈ Algebra.adjoin ℤ {Hom.ofIsogeny (frobeniusIsogeny W.toAffine)} := by
  set π := Hom.ofIsogeny (frobeniusIsogeny W.toAffine)
  -- `v = 2π - a` is anti-self-dual, since `π̂ = a - π`
  set v : Hom W.toAffine W.toAffine := 2 • π - W.frobeniusTrace • 1 with hv_def
  have hv : v.dual = -v := by
    rw [hv_def, Hom.dual_sub, Hom.dual_nsmul, Hom.dual_zsmul, Hom.dual_ofIsogeny,
      dual_frobeniusIsogeny, ofIsogeny_dualFrobeniusIsogeny, Hom.one_def, Hom.dual_id]
    abel
  -- `v ≠ 0`, as `1` and `π` are linearly independent on an ordinary curve
  have hv₀ : v ≠ 0 := by
    intro h
    have hli := (linearIndependent_one_ofIsogeny_frobeniusIsogeny_iff W.toAffine).2 fun h' ↦
      not_isSupersingular.2 hW <|
        isSupersingular_of_ofIsogeny_frobeniusIsogeny_mem_range_intCast p W h'
    have := LinearIndependent.pair_iff.1 hli (-W.frobeniusTrace) 2 (by
      rw [← h, hv_def, two_zsmul, two_nsmul, neg_smul]; abel)
    omega
  refine ⟨4 * v.degree,
    mul_ne_zero four_ne_zero (Nat.cast_ne_zero.2 ((v.degree_eq_zero_iff).not.2 hv₀)), fun f ↦ ?_⟩
  -- `u = 2f - t` is anti-self-dual, where `f̂ + f = t`
  set t := QuadraticMap.polar (fun h : Hom W.toAffine W.toAffine ↦ (h.degree : ℤ)) f 1
  have ht : f.dual = t • 1 - f := by
    have h := Hom.dual_comp_add_dual_comp f (Hom.id _)
    rw [Hom.comp_id, Hom.dual_id, Hom.id_comp, ← Hom.one_def] at h
    rw [← h, add_sub_cancel_right]
  set u : Hom W.toAffine W.toAffine := 2 • f - t • 1 with hu_def
  have hu : u.dual = -u := by
    rw [hu_def, Hom.dual_sub, Hom.dual_nsmul, Hom.dual_zsmul, ht, Hom.one_def, Hom.dual_id]
    abel
  -- `(u + v)² = u² + 2uv + v²`, with all three squares integers, so `2uv` is an integer `e`
  have huv : u * v = v * u := mul_comm_of_isOrdinary hW u v
  have h2 := mul_self_eq_neg_degree (x := u + v) (by rw [Hom.dual_add, hu, hv, neg_add])
  rw [add_mul, mul_add, mul_add, ← huv, mul_self_eq_neg_degree hu, mul_self_eq_neg_degree hv]
    at h2
  set e : ℤ := u.degree + v.degree - (u + v).degree
  have he : 2 • (u * v) = e • 1 := by
    rw [two_nsmul, sub_smul, add_smul]
    linear_combination (norm := abel_nf) h2
  -- multiplying by `v` gives `2 deg v • u = -e • v`
  have key : (2 * (v.degree : ℤ)) • u = -(e • v) := by
    have h3 := congrArg (· * v) he
    simp only [smul_mul_assoc, mul_assoc, mul_self_eq_neg_degree hv, mul_neg, mul_smul_comm,
      mul_one, one_mul] at h3
    rw [← h3, smul_neg, neg_neg, mul_smul, two_zsmul, two_nsmul]
  -- so `4 deg v • f = 2 deg v t - e v` lies in `ℤ[π]`
  have hf : (4 * (v.degree : ℤ)) • f = (2 * v.degree * t) • 1 - e • v := by
    rw [sub_eq_add_neg, ← key, hu_def]
    module
  rw [hf]
  have hπ : π ∈ Algebra.adjoin ℤ {π} := Algebra.subset_adjoin rfl
  exact sub_mem (zsmul_mem (one_mem _) _) (zsmul_mem (sub_mem (nsmul_mem hπ 2)
    (zsmul_mem (one_mem _) _)) _)

/-- On an ordinary curve, multiplication by a suitable nonzero integer embeds the endomorphism
ring `ℤ`-linearly into `ℤ[π]`. -/
private theorem exists_injective_linearMap_toSubmodule_adjoin (hW : W.IsOrdinary p) :
    ∃ g : Hom W.toAffine W.toAffine →ₗ[ℤ]
      Subalgebra.toSubmodule (Algebra.adjoin ℤ {Hom.ofIsogeny (frobeniusIsogeny W.toAffine)}),
      Function.Injective g := by
  obtain ⟨N, hN, h⟩ := exists_zsmul_mem_adjoin_ofIsogeny_frobeniusIsogeny_of_isOrdinary hW
  exact ⟨(N • LinearMap.id).codRestrict _ h, fun f f' hff' ↦
    smul_right_injective _ hN (congrArg Subtype.val hff')⟩

/-- **The endomorphism ring of an ordinary curve over a finite field is a finitely generated
`ℤ`-module** (Silverman III.7.5, V.3.1): it embeds into `ℤ[π] = ℤ + ℤπ`. -/
theorem module_finite_hom_of_isOrdinary (hW : W.IsOrdinary p) :
    Module.Finite ℤ (Hom W.toAffine W.toAffine) := by
  obtain ⟨g, hg⟩ := exists_injective_linearMap_toSubmodule_adjoin hW
  -- `ℤ[π]` is spanned by `1` and `π`
  have : Module.Finite ℤ (Subalgebra.toSubmodule
      (Algebra.adjoin ℤ {Hom.ofIsogeny (frobeniusIsogeny W.toAffine)})) := by
    rw [toSubmodule_adjoin_ofIsogeny_frobeniusIsogeny]
    exact Module.Finite.span_of_finite ℤ (Set.toFinite _)
  exact Module.Finite.of_injective g hg

/-- **The endomorphism ring of an ordinary curve over a finite field has rank `2`** (Silverman
V.3.1, III.9.4): it contains `ℤ[π]`, of rank `2`, and embeds into it. With
`WeierstrassCurve.mul_comm_of_isOrdinary`, it is an order in the imaginary quadratic field
`ℚ(π)`. -/
theorem finrank_hom_of_isOrdinary (hW : W.IsOrdinary p) :
    Module.finrank ℤ (Hom W.toAffine W.toAffine) = 2 := by
  have := module_finite_hom_of_isOrdinary hW
  have h2 := finrank_adjoin_ofIsogeny_frobeniusIsogeny_of_isOrdinary p W hW
  rw [← Subalgebra.finrank_toSubmodule] at h2
  obtain ⟨g, hg⟩ := exists_injective_linearMap_toSubmodule_adjoin hW
  exact le_antisymm (h2 ▸ LinearMap.finrank_le_finrank_of_injective hg)
    (h2 ▸ Submodule.finrank_le _)

end WeierstrassCurve

end
