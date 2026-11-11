/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Dehn twists of amalgamated products

For a two-factor pushout, a parameter in the right factor centralizing the image of the
amalgamating group defines an automorphism fixing the left factor and conjugating the right
factor by that parameter. The inverse uses the inverse parameter, and composition follows
multiplication of parameters in the same order. When the boundary maps are injective, the
twist is the identity exactly when its parameter is central in the right factor.

The construction works even for noninjective boundary maps; only the converse identity
criterion needs injectivity. The two factors are indexed by `false` and `true`. Subgroup
image formulas express preservation of their conjugacy classes, as used in modular groups
of one-edge splittings. The construction uses Mathlib's `Monoid.PushoutI.lift`.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, §5.1.4 and §9.
* J.-P. Serre, *Trees*, Chapter I, §1.1 (the amalgam universal property).
-/

public section

namespace Monoid.PushoutI

variable {G : Bool → Type*} {C : Type*} [∀ i, Group (G i)] [Group C]
    (φ : ∀ i, C →* G i)

private def twistFactor (z : G true) : ∀ i, G i →* PushoutI φ
  | false => of false
  | true => (of true).comp (MulAut.conj z).toMonoidHom

private theorem twistFactor_false (z : G true) (a : G false) :
    twistFactor φ z false a = of false a := rfl

private theorem twistFactor_true (z : G true) (b : G true) :
    twistFactor φ z true b = of true z * of true b * (of true z)⁻¹ := by
  simp [twistFactor, MulAut.conj_apply]

private def twistHom (z : Subgroup.centralizer (Set.range (φ true))) :
    PushoutI φ →* PushoutI φ :=
  lift (twistFactor φ z) (base φ) fun i => by
    ext c
    cases i
    · exact of_apply_eq_base φ false c
    · have h := (Subgroup.mem_centralizer_iff.mp z.property) (φ true c)
        ⟨c, rfl⟩
      simpa [twistFactor, MulAut.conj_apply, ← h, mul_assoc] using of_apply_eq_base φ true c

private theorem twistHom_of_false
    (z : Subgroup.centralizer (Set.range (φ true))) (a : G false) :
    twistHom φ z (of false a) = of false a := by
  rw [twistHom, lift_of, twistFactor_false]

private theorem twistHom_of_true
    (z : Subgroup.centralizer (Set.range (φ true))) (b : G true) :
    twistHom φ z (of true b) = of true z * of true b * (of true z)⁻¹ := by
  rw [twistHom, lift_of, twistFactor_true]

private theorem twistHom_comp
    (z w : Subgroup.centralizer (Set.range (φ true))) :
    (twistHom φ z).comp (twistHom φ w) = twistHom φ (z * w) := by
  apply hom_ext_nonempty
  intro i
  ext g
  cases i
  · simp only [MonoidHom.comp_apply, twistHom_of_false]
  · simp only [MonoidHom.comp_apply, twistHom_of_true, map_mul, map_inv, Subgroup.coe_mul]
    simp [mul_assoc]

private theorem twistHom_one : twistHom φ 1 = MonoidHom.id _ := by
  apply hom_ext_nonempty
  intro i
  ext g
  cases i
  · simp [twistHom_of_false]
  · simp [twistHom_of_true]

/-- The Dehn twist fixing the left factor and conjugating the right factor by `z`.
The parameter centralizes the right-hand image of the amalgamating group. -/
def dehnTwist (z : Subgroup.centralizer (Set.range (φ true))) :
    MulAut (PushoutI φ) :=
  MonoidHom.toMulEquiv (twistHom φ z) (twistHom φ z⁻¹)
    (by rw [twistHom_comp, inv_mul_cancel, twistHom_one])
    (by rw [twistHom_comp, mul_inv_cancel, twistHom_one])

/-- The left factor is fixed pointwise. -/
@[simp] theorem dehnTwist_of_false
    (z : Subgroup.centralizer (Set.range (φ true))) (a : G false) :
    dehnTwist φ z (of false a) = of false a := twistHom_of_false φ z a

/-- The right factor is conjugated by the image of the parameter. -/
@[simp] theorem dehnTwist_of_true
    (z : Subgroup.centralizer (Set.range (φ true))) (b : G true) :
    dehnTwist φ z (of true b) = of true z * of true b * (of true z)⁻¹ :=
  twistHom_of_true φ z b

/-- The amalgamating group is fixed pointwise. -/
@[simp] theorem dehnTwist_base
    (z : Subgroup.centralizer (Set.range (φ true))) (c : C) :
    dehnTwist φ z (base φ c) = base φ c := by
  rw [← of_apply_eq_base φ false, dehnTwist_of_false]

/-- The parameter one gives the identity twist. -/
@[simp] theorem dehnTwist_one : dehnTwist φ 1 = 1 :=
  MulEquiv.toMonoidHom_injective (twistHom_one φ)

/-- Composition has the same order as multiplication of the parameters in the right factor. -/
@[simp] theorem dehnTwist_mul
    (z w : Subgroup.centralizer (Set.range (φ true))) :
    dehnTwist φ (z * w) = dehnTwist φ z * dehnTwist φ w :=
  MulEquiv.toMonoidHom_injective (twistHom_comp φ z w).symm

/-- Inverting the parameter gives the inverse twist. -/
@[simp] theorem dehnTwist_inv
    (z : Subgroup.centralizer (Set.range (φ true))) :
    dehnTwist φ z⁻¹ = (dehnTwist φ z)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← dehnTwist_mul, inv_mul_cancel, dehnTwist_one]

/-- A parameter central in the right factor gives the identity twist, even without
injective boundary maps. -/
theorem dehnTwist_eq_one_of_mem_center
    (z : Subgroup.centralizer (Set.range (φ true)))
    (hz : (z : G true) ∈ Subgroup.center (G true)) : dehnTwist φ z = 1 := by
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext_nonempty
  intro i
  ext g
  cases i
  · simp
  · have h := congrArg (of (φ := φ) true) ((Subgroup.mem_center_iff.mp hz) g)
    simp only [map_mul] at h
    simp [← h, mul_assoc]

/-- For an amalgamated product with injective boundary maps, a twist is the identity
exactly when its parameter is central in the right factor. -/
@[simp] theorem dehnTwist_eq_one_iff
    (hφ : ∀ i, Function.Injective (φ i))
    (z : Subgroup.centralizer (Set.range (φ true))) :
    dehnTwist φ z = 1 ↔ (z : G true) ∈ Subgroup.center (G true) := by
  refine ⟨fun h => Subgroup.mem_center_iff.mpr fun g => ?_,
    dehnTwist_eq_one_of_mem_center φ z⟩
  apply of_injective hφ true
  have hg := congrArg (fun f : MulAut (PushoutI φ) => f (of true g)) h
  have hzg := mul_inv_eq_iff_eq_mul.mp
    (by simpa only [dehnTwist_of_true, MulAut.one_apply] using hg)
  simpa only [← map_mul] using hzg.symm

/-- Every subgroup of the left factor is fixed. -/
@[simp] theorem map_dehnTwist_map_of_false
    (z : Subgroup.centralizer (Set.range (φ true))) (K : Subgroup (G false)) :
    (K.map (of (φ := φ) false)).map (dehnTwist φ z : PushoutI φ →* PushoutI φ) =
      K.map (of false) := by
  rw [Subgroup.map_map]
  congr 1

/-- Every subgroup of the right factor is carried to its conjugate by the parameter. -/
@[simp] theorem map_dehnTwist_map_of_true
    (z : Subgroup.centralizer (Set.range (φ true))) (K : Subgroup (G true)) :
    (K.map (of (φ := φ) true)).map (dehnTwist φ z : PushoutI φ →* PushoutI φ) =
      (K.map (of true)).map (MulAut.conj (of (φ := φ) true z) : PushoutI φ →* PushoutI φ) := by
  simp only [Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply]

end Monoid.PushoutI
