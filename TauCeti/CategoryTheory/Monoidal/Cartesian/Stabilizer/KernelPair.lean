/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Monoidal.Cartesian.Stabilizer.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The relation defined by an orbit morphism

For an internal group action and a global point `x`, let `H` be its scheme-theoretic
stabilizer. The morphism `(g, h) ↦ (g, gh)` identifies `G × H` with `G ×_X G`, the
kernel pair of the orbit morphism. Its inverse is `(g, g') ↦ (g, g⁻¹g')`.
Thus the relation defined by the orbit morphism is right multiplication by the
stabilizer, on arbitrary test objects, including nonreduced schemes.

The result holds in any cartesian monoidal category with the stabilizer pullback.
It does not require the orbit morphism to be an epimorphism or a quotient to exist.
For scheme actions this provides the relation used in identifying a represented
orbit with the homogeneous space of left stabilizer cosets `G ⧸ H`.

The proof uses the same pullback-cone construction as
`TauCeti.isPullback_mul_of_isPullback_one`, for group homomorphisms; here the
orbit morphism need not be a group homomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 7, orbits and homogeneous spaces.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ModObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (G : C) {X : C} [GrpObj G] [ModObj G X] (x : 𝟙_ C ⟶ X)

namespace stabilizer

variable [HasPullback (orbitMap G x) x]

/-- Right multiplication of `G` by the stabilizer of `x`, as an internal morphism. -/
def rightMul : G ⊗ stabilizer G x ⟶ G :=
  fst _ _ * (snd _ _ ≫ incl G x)

/-- Right multiplication is the product of the group coordinate and the included
stabilizer coordinate. -/
theorem rightMul_def : rightMul G x = fst _ _ * (snd _ _ ≫ incl G x) :=
  (rfl)

/-- Composing with right multiplication multiplies the two coordinates in the group. -/
@[reassoc (attr := simp)]
theorem comp_rightMul {T : C} (f : T ⟶ G ⊗ stabilizer G x) :
    f ≫ rightMul G x = (f ≫ fst _ _) * (f ≫ snd _ _ ≫ incl G x) := by
  simp only [rightMul_def, MonObj.comp_mul]

/-- Right multiplication by a stabilizing point leaves the orbit morphism unchanged. -/
@[reassoc]
theorem rightMul_orbitMap :
    rightMul G x ≫ orbitMap G x = fst G (stabilizer G x) ≫ orbitMap G x := by
  rw [comp_orbitMap, rightMul_def, SemigroupAction.mul_smul]
  have h := comp_mem_stabilizerPoints G x (snd G (stabilizer G x)) (incl_mem G x)
  rw [MulAction.mem_stabilizer_iff] at h
  rw [h, ← comp_orbitMap]

/-- The kernel pair of an orbit morphism is the relation of right multiplication by
the stabilizer: its projections are `(g,h) ↦ g` and `(g,h) ↦ gh`. -/
theorem isPullback_rightMul :
    IsPullback (fst G (stabilizer G x)) (rightMul G x) (orbitMap G x) (orbitMap G x) := by
  refine IsPullback.of_isLimit' ⟨(rightMul_orbitMap G x).symm⟩ ?_
  let k (s : PullbackCone (orbitMap G x) (orbitMap G x)) : s.pt ⟶ stabilizer G x :=
    stabilizer.lift G x (s.fst⁻¹ * s.snd)
      ((inv_mul_mem_stabilizerPoints_iff G x s.fst s.snd).mpr s.condition)
  have hk (s : PullbackCone (orbitMap G x) (orbitMap G x)) :
      k s ≫ incl G x = s.fst⁻¹ * s.snd := by
    simp [k]
  refine PullbackCone.IsLimit.mk _ (fun s ↦ CartesianMonoidalCategory.lift s.fst (k s))
    (fun s ↦ by simp) (fun s ↦ by simp [hk]) ?_
  intro s m hm₁ hm₂
  apply CartesianMonoidalCategory.hom_ext
  · simpa using hm₁
  · apply (cancel_mono (incl G x)).mp
    have hm : s.fst * (m ≫ snd _ _ ≫ incl G x) = s.snd := by
      simpa only [comp_rightMul, hm₁] using hm₂
    simp only [lift_snd, hk]
    rw [Category.assoc]
    exact (eq_inv_mul_iff_mul_eq).mpr hm

variable [HasPullback (orbitMap G x) (orbitMap G x)]

/-- The actual isomorphism from the product with the stabilizer to the fibre product
of the orbit morphism with itself, sending `(g,h)` to `(g,gh)`. -/
def kernelPairIso :
    G ⊗ stabilizer G x ≅ pullback (orbitMap G x) (orbitMap G x) :=
  (isPullback_rightMul G x).isoPullback

@[reassoc (attr := simp)]
theorem kernelPairIso_hom_fst :
    (kernelPairIso G x).hom ≫ pullback.fst _ _ = fst G (stabilizer G x) :=
  (isPullback_rightMul G x).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem kernelPairIso_hom_snd :
    (kernelPairIso G x).hom ≫ pullback.snd _ _ = rightMul G x :=
  (isPullback_rightMul G x).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem kernelPairIso_inv_fst :
    (kernelPairIso G x).inv ≫ fst G (stabilizer G x) = pullback.fst _ _ :=
  (isPullback_rightMul G x).isoPullback_inv_fst

/-- The stabilizer coordinate of the inverse is the quotient `g⁻¹g'`, in that order. -/
@[reassoc (attr := simp)]
theorem kernelPairIso_inv_snd_incl :
    (kernelPairIso G x).inv ≫ snd G (stabilizer G x) ≫ incl G x =
      (pullback.fst (orbitMap G x) (orbitMap G x))⁻¹ * pullback.snd _ _ := by
  have h := (isPullback_rightMul G x).isoPullback_inv_snd
  rw [← kernelPairIso, comp_rightMul, kernelPairIso_inv_fst] at h
  exact (eq_inv_mul_iff_mul_eq).mpr h

end stabilizer

end TauCeti
