/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Iwasawa
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The Iwasawa decomposition of `SL n ℝ`

Every real matrix of determinant one factors uniquely as `g = k a u`, with `k` special orthogonal,
`a` diagonal with positive diagonal entries and determinant one, and `u` upper unitriangular, and
the three factors depend continuously on `g`. This is the Iwasawa decomposition `G = K A N` of the
real Lie group `G = SL n ℝ`, with maximal compact subgroup `K = SO(n)`, `A` the positive
diagonal matrices of determinant one, and `N` the upper unitriangular matrices.

The three factors are the preimages under `Matrix.SpecialLinearGroup.toGL` of the three factors
`unitarySubgroup (GL (Fin n) ℝ)`, `TauCeti.posDiagonalSubgroup (Fin n) ℝ` and
`TauCeti.upperUnitriangularGroup (Fin n) ℝ` of the Iwasawa decomposition `TauCeti.iwasawaHomeomorph`
of `GL n ℝ`; the first preimage is `SO(n)` by `TauCeti.toGL_mem_unitarySubgroup_iff`. The
homeomorphism `TauCeti.iwasawaSLHomeomorph n : K × A × N ≃ₜ SL n ℝ` is given by multiplication, and
its inverse is the restriction of the inverse for `GL n ℝ`
(`TauCeti.iwasawaHomeomorph_symm_toGL`).

## The restriction

Let `g = k a u` be the decomposition of `g` in `GL n ℝ`. The factor `u` has determinant one, `a`
has positive determinant, and `k` has determinant `±1`, being orthogonal. So `det g = 1` forces
`det k = det a = 1`: the three factors already lie in `SL n ℝ`, and the decomposition of `GL n ℝ`
restricts to `SL n ℝ`. Continuity of the factors follows from continuity for `GL n ℝ`, because
`SL n ℝ` carries the topology induced along `toGL` (`Matrix.SpecialLinearGroup.isEmbedding_toGL`).

## Main definitions

* `TauCeti.iwasawaSLHomeomorph n`: the Iwasawa decomposition, the homeomorphism
  `SO(n) × A × N ≃ₜ SL n ℝ` sending `(k, a, u)` to `k a u`.

## Main results

* `TauCeti.iwasawaSLHomeomorph_apply`: the decomposition multiplies the three factors.
* `TauCeti.iwasawaHomeomorph_symm_toGL`: the factors of a determinant-one matrix in `GL n ℝ` are
  the images of its factors in `SL n ℝ`.
* `Matrix.SpecialLinearGroup.existsUnique_iwasawa`: every real matrix of determinant one is
  uniquely `k a u`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002,
  Section VI.4 (the Iwasawa decomposition).
-/

public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup

namespace TauCeti

variable {n : ℕ}

/-- If `k a u` has determinant one, for `k` orthogonal, `a` positive diagonal and `u` upper
unitriangular, then `k` and `a` have determinant one. -/
private theorem det_eq_one_of_det_mul_mul_eq_one {k a u : GL (Fin n) ℝ}
    (hk : k ∈ unitarySubgroup (GL (Fin n) ℝ)) (ha : a ∈ posDiagonalSubgroup (Fin n) ℝ)
    (hu : u ∈ upperUnitriangularGroup (Fin n) ℝ)
    (h : GeneralLinearGroup.det (k * a * u) = 1) :
    GeneralLinearGroup.det k = 1 ∧ GeneralLinearGroup.det a = 1 := by
  simp only [Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_mul, det_mul,
    (UpperUnitriangularGroup.mem_iff.1 hu).det_eq_one, mul_one, Units.val_one] at h ⊢
  obtain ⟨d, hd, had⟩ := mem_posDiagonalSubgroup_iff.1 ha
  have ha₀ : 0 < (a : Matrix (Fin n) (Fin n) ℝ).det := by
    rw [had, det_diagonal]
    exact Finset.prod_pos fun i _ => hd i
  -- `k kᵀ = 1`, so `det k` squares to one; it is positive since `det k * det a = 1`.
  have hk₂ : (k : Matrix (Fin n) (Fin n) ℝ).det * (k : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
    simpa [det_transpose] using congrArg det (mem_unitarySubgroup_GL_iff.1 hk)
  have hk₀ : 0 < (k : Matrix (Fin n) (Fin n) ℝ).det := by
    by_contra hneg
    nlinarith
  obtain hk₁ | hk₁ := mul_self_eq_one_iff.1 hk₂
  · exact ⟨hk₁, by rwa [hk₁, one_mul] at h⟩
  · linarith

/-- The Iwasawa factors in `GL n ℝ` of a matrix of determinant one. -/
private def slFactors (g : SpecialLinearGroup (Fin n) ℝ) :
    unitarySubgroup (GL (Fin n) ℝ) × posDiagonalSubgroup (Fin n) ℝ ×
      upperUnitriangularGroup (Fin n) ℝ :=
  (iwasawaHomeomorph n).symm (toGL g)

private theorem slFactors_mul (g : SpecialLinearGroup (Fin n) ℝ) :
    ((slFactors g).1 : GL (Fin n) ℝ) * (slFactors g).2.1 * (slFactors g).2.2 = toGL g := by
  rw [← iwasawaHomeomorph_apply, slFactors, Homeomorph.apply_symm_apply]

private theorem det_slFactors (g : SpecialLinearGroup (Fin n) ℝ) :
    GeneralLinearGroup.det ((slFactors g).1 : GL (Fin n) ℝ) = 1 ∧
      GeneralLinearGroup.det ((slFactors g).2.1 : GL (Fin n) ℝ) = 1 :=
  det_eq_one_of_det_mul_mul_eq_one (slFactors g).1.2 (slFactors g).2.1.2 (slFactors g).2.2.2
    (by rw [slFactors_mul, coeToGL_det])

private theorem det_slFactors_unitriangular (g : SpecialLinearGroup (Fin n) ℝ) :
    GeneralLinearGroup.det ((slFactors g).2.2 : GL (Fin n) ℝ) = 1 :=
  Units.ext <| by
    rw [GeneralLinearGroup.val_det_apply, Units.val_one,
      (UpperUnitriangularGroup.mem_iff.1 (slFactors g).2.2.2).det_eq_one]

/-- The special orthogonal factor of the Iwasawa decomposition of `g`. -/
private def slOrthogonal (g : SpecialLinearGroup (Fin n) ℝ) : SpecialLinearGroup (Fin n) ℝ :=
  toGLKerEquiv.symm ⟨(slFactors g).1, (det_slFactors g).1⟩

/-- The positive diagonal factor of the Iwasawa decomposition of `g`. -/
private def slDiagonal (g : SpecialLinearGroup (Fin n) ℝ) : SpecialLinearGroup (Fin n) ℝ :=
  toGLKerEquiv.symm ⟨(slFactors g).2.1, (det_slFactors g).2⟩

/-- The upper unitriangular factor of the Iwasawa decomposition of `g`. -/
private def slUnitriangular (g : SpecialLinearGroup (Fin n) ℝ) : SpecialLinearGroup (Fin n) ℝ :=
  toGLKerEquiv.symm ⟨(slFactors g).2.2, det_slFactors_unitriangular g⟩

private theorem toGL_slOrthogonal (g : SpecialLinearGroup (Fin n) ℝ) :
    toGL (slOrthogonal g) = (slFactors g).1 :=
  congrArg Subtype.val (toGLKerEquiv.apply_symm_apply _)

private theorem toGL_slDiagonal (g : SpecialLinearGroup (Fin n) ℝ) :
    toGL (slDiagonal g) = (slFactors g).2.1 :=
  congrArg Subtype.val (toGLKerEquiv.apply_symm_apply _)

private theorem toGL_slUnitriangular (g : SpecialLinearGroup (Fin n) ℝ) :
    toGL (slUnitriangular g) = (slFactors g).2.2 :=
  congrArg Subtype.val (toGLKerEquiv.apply_symm_apply _)

/-- The Iwasawa factors in `GL n ℝ` of `k a u` are `k`, `a` and `u`, for `k`, `a`, `u` in the three
factors of `SL n ℝ`. -/
private theorem slFactors_mul_mul {k a u : SpecialLinearGroup (Fin n) ℝ}
    (hk : toGL k ∈ unitarySubgroup (GL (Fin n) ℝ)) (ha : toGL a ∈ posDiagonalSubgroup (Fin n) ℝ)
    (hu : toGL u ∈ upperUnitriangularGroup (Fin n) ℝ) :
    slFactors (k * a * u) = (⟨toGL k, hk⟩, ⟨toGL a, ha⟩, ⟨toGL u, hu⟩) :=
  (iwasawaHomeomorph n).symm_apply_eq.2 <| by rw [iwasawaHomeomorph_apply, map_mul, map_mul]

variable (n) in
/-- **The Iwasawa decomposition of `SL n ℝ`.** Multiplication `(k, a, u) ↦ k a u` is a
homeomorphism from the product of the special orthogonal group, the positive diagonal matrices of
determinant one and the upper unitriangular matrices onto `SL n ℝ`. The three factors are the
preimages under `toGL` of the three factors of the Iwasawa decomposition of `GL n ℝ`. -/
def iwasawaSLHomeomorph :
    (unitarySubgroup (GL (Fin n) ℝ)).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _) ×
        (posDiagonalSubgroup (Fin n) ℝ).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _) ×
        (upperUnitriangularGroup (Fin n) ℝ).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _) ≃ₜ
      SpecialLinearGroup (Fin n) ℝ where
  toFun x := x.1 * x.2.1 * x.2.2
  invFun g :=
    (⟨slOrthogonal g, Subgroup.mem_comap.2 <| (toGL_slOrthogonal g).symm ▸ (slFactors g).1.2⟩,
      ⟨slDiagonal g, Subgroup.mem_comap.2 <| (toGL_slDiagonal g).symm ▸ (slFactors g).2.1.2⟩,
      ⟨slUnitriangular g,
        Subgroup.mem_comap.2 <| (toGL_slUnitriangular g).symm ▸ (slFactors g).2.2.2⟩)
  left_inv := by
    rintro ⟨⟨k, hk⟩, ⟨a, ha⟩, ⟨u, hu⟩⟩
    have h := slFactors_mul_mul (Subgroup.mem_comap.1 hk) (Subgroup.mem_comap.1 ha)
      (Subgroup.mem_comap.1 hu)
    -- each factor of `k * a * u` maps under `toGL` to the corresponding factor in `GL n ℝ`
    have hK : slOrthogonal (k * a * u) = k := toGL_injective <| by
      rw [toGL_slOrthogonal, h]
    have hA : slDiagonal (k * a * u) = a := toGL_injective <| by
      rw [toGL_slDiagonal, h]
    have hU : slUnitriangular (k * a * u) = u := toGL_injective <| by
      rw [toGL_slUnitriangular, h]
    exact Prod.ext (Subtype.ext hK) (Prod.ext (Subtype.ext hA) (Subtype.ext hU))
  right_inv g := toGL_injective <| by
    rw [map_mul, map_mul, toGL_slOrthogonal, toGL_slDiagonal, toGL_slUnitriangular, slFactors_mul]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hF : Continuous (slFactors (n := n)) :=
      (iwasawaHomeomorph n).symm.continuous.comp continuous_toGL
    have hK : Continuous (slOrthogonal (n := n)) := isEmbedding_toGL.continuous_iff.2 <| by
      simpa only [Function.comp_def, toGL_slOrthogonal] using
        continuous_subtype_val.comp (continuous_fst.comp hF)
    have hA : Continuous (slDiagonal (n := n)) := isEmbedding_toGL.continuous_iff.2 <| by
      simpa only [Function.comp_def, toGL_slDiagonal] using
        continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp hF))
    have hU : Continuous (slUnitriangular (n := n)) := isEmbedding_toGL.continuous_iff.2 <| by
      simpa only [Function.comp_def, toGL_slUnitriangular] using
        continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp hF))
    exact (hK.subtype_mk _).prodMk ((hA.subtype_mk _).prodMk (hU.subtype_mk _))

/-- The Iwasawa decomposition of `SL n ℝ` multiplies its three factors. -/
@[simp]
theorem iwasawaSLHomeomorph_apply
    (x : (unitarySubgroup (GL (Fin n) ℝ)).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _) ×
      (posDiagonalSubgroup (Fin n) ℝ).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _) ×
      (upperUnitriangularGroup (Fin n) ℝ).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _)) :
    iwasawaSLHomeomorph n x = x.1 * x.2.1 * x.2.2 :=
  (rfl)

/-- **The Iwasawa decomposition of `GL n ℝ` restricts to `SL n ℝ`**: the factors in `GL n ℝ` of a
matrix of determinant one are the images under `toGL` of its factors in `SL n ℝ`. -/
theorem iwasawaHomeomorph_symm_toGL (g : SpecialLinearGroup (Fin n) ℝ) :
    (iwasawaHomeomorph n).symm (toGL g) =
      (⟨toGL ((iwasawaSLHomeomorph n).symm g).1, ((iwasawaSLHomeomorph n).symm g).1.2⟩,
        ⟨toGL ((iwasawaSLHomeomorph n).symm g).2.1, ((iwasawaSLHomeomorph n).symm g).2.1.2⟩,
        ⟨toGL ((iwasawaSLHomeomorph n).symm g).2.2, ((iwasawaSLHomeomorph n).symm g).2.2.2⟩) :=
  (iwasawaHomeomorph n).symm_apply_eq.2 <| by
    conv_lhs => rw [← (iwasawaSLHomeomorph n).apply_symm_apply g]
    rw [iwasawaSLHomeomorph_apply, iwasawaHomeomorph_apply, map_mul, map_mul]

end TauCeti

namespace Matrix.SpecialLinearGroup

open TauCeti

/-- **Every real matrix of determinant one is uniquely `k a u`**, with `k` special orthogonal, `a`
diagonal with positive diagonal entries and `u` upper unitriangular, all three of determinant
one. -/
theorem existsUnique_iwasawa {n : ℕ} (g : SpecialLinearGroup (Fin n) ℝ) :
    ∃! x : (unitarySubgroup (GL (Fin n) ℝ)).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _) ×
        (posDiagonalSubgroup (Fin n) ℝ).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _) ×
        (upperUnitriangularGroup (Fin n) ℝ).comap (toGL : SpecialLinearGroup (Fin n) ℝ →* _),
      (x.1 : SpecialLinearGroup (Fin n) ℝ) * x.2.1 * x.2.2 = g :=
  (iwasawaSLHomeomorph n).bijective.existsUnique g

end Matrix.SpecialLinearGroup
