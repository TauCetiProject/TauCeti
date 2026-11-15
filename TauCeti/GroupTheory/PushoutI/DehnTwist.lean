/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PushoutI.Basic

/-!
# Dehn twists of amalgamated products

For a two-factor pushout, a parameter in the right factor centralizing the image of the
amalgamating group defines an automorphism fixing the left factor and conjugating the right
factor by that parameter. The inverse uses the inverse parameter, and composition follows
multiplication of parameters in the same order. When the boundary maps are injective, the
twist is the identity exactly when its parameter is central in the right factor.

The construction works even for noninjective boundary maps; the identity criterion and the
necessity of the centralizer hypothesis need injectivity. The two factors are indexed by `false`
and `true`. Subgroup image formulas express preservation of their conjugacy classes, as used in
modular groups of one-edge splittings. The construction uses Mathlib's `Monoid.PushoutI.lift`.

The centralizer hypothesis is necessary: with injective boundary maps, the rule fixing the left
factor and conjugating the right factor by an element `z` of the right factor extends to an
endomorphism exactly when `z` centralizes the image of the amalgamating group
(`Monoid.PushoutI.exists_map_of_true_eq_iff_mem_centralizer`).

A parameter in the *left* factor centralizing the image of the amalgamating group also defines
an automorphism fixing the left factor and conjugating the right factor
(`Monoid.PushoutI.leftDehnTwist`). These twists fix their own parameters, so they compose in the
order opposite to multiplication of parameters. On the images of an element of the amalgamating
group the two families agree; this is the twist of `A ∗_C B` by a central element of `C`.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, §5.1.4 and §9.
* J.-P. Serre, *Trees*, Chapter I, §1.1 (the amalgam universal property).
-/

public section

namespace Monoid.PushoutI

variable {G : Bool → Type*} {C : Type*} [∀ i, Group (G i)] [Group C]
    (φ : ∀ i, C →* G i)

private def twistFactor (g : PushoutI φ) : ∀ i, G i →* PushoutI φ
  | false => of false
  | true => (MulAut.conj g).toMonoidHom.comp (of true)

/-- The endomorphism fixing the left factor and conjugating the right factor by an element `g`
of the pushout commuting with the amalgamating group. -/
private def twistHom (g : PushoutI φ) (hg : ∀ c, Commute g (base φ c)) :
    PushoutI φ →* PushoutI φ :=
  lift (twistFactor φ g) (base φ) fun i => by
    ext c
    cases i
    · exact of_apply_eq_base φ false c
    · simpa [twistFactor, MulAut.conj_apply, of_apply_eq_base] using
        mul_inv_eq_iff_eq_mul.mpr (hg c).eq

private theorem twistHom_of_false (g : PushoutI φ) (hg : ∀ c, Commute g (base φ c))
    (a : G false) : twistHom φ g hg (of false a) = of false a := by
  simp [twistHom, twistFactor]

private theorem twistHom_of_true (g : PushoutI φ) (hg : ∀ c, Commute g (base φ c))
    (b : G true) : twistHom φ g hg (of true b) = g * of true b * g⁻¹ := by
  simp [twistHom, twistFactor, MulAut.conj_apply]

private theorem twistHom_comp {g h k : PushoutI φ} (hg : ∀ c, Commute g (base φ c))
    (hh : ∀ c, Commute h (base φ c)) (hk : ∀ c, Commute k (base φ c))
    (e : twistHom φ g hg h * g = k) :
    (twistHom φ g hg).comp (twistHom φ h hh) = twistHom φ k hk := by
  apply hom_ext_nonempty
  intro i
  ext b
  cases i
  · simp [twistHom_of_false]
  · simp [twistHom_of_true, ← e, mul_assoc]

private theorem twistHom_one : twistHom φ 1 (fun _ => Commute.one_left _) = MonoidHom.id _ := by
  apply hom_ext_nonempty
  intro i
  ext b
  cases i
  · simp [twistHom_of_false]
  · simp [twistHom_of_true]

/-- The endomorphism underlying the twist by a parameter of the right factor. -/
private abbrev rightHom (z : Subgroup.centralizer (Set.range (φ true))) :
    PushoutI φ →* PushoutI φ :=
  twistHom φ (of true (z : G true)) (commute_of_base_of_mem_centralizer z.property)

private theorem rightHom_comp (z w : Subgroup.centralizer (Set.range (φ true))) :
    (rightHom φ z).comp (rightHom φ w) = rightHom φ (z * w) :=
  twistHom_comp φ _ _ _ (by simp [twistHom_of_true])

private theorem rightHom_one : rightHom φ 1 = MonoidHom.id _ := by
  simpa [rightHom] using twistHom_one φ

/-- The Dehn twist fixing the left factor and conjugating the right factor by `z`.
The parameter centralizes the right-hand image of the amalgamating group. -/
def dehnTwist (z : Subgroup.centralizer (Set.range (φ true))) :
    MulAut (PushoutI φ) :=
  MonoidHom.toMulEquiv (rightHom φ z) (rightHom φ z⁻¹)
    (by rw [rightHom_comp, inv_mul_cancel, rightHom_one])
    (by rw [rightHom_comp, mul_inv_cancel, rightHom_one])

/-- The left factor is fixed pointwise. -/
@[simp] theorem dehnTwist_of_false
    (z : Subgroup.centralizer (Set.range (φ true))) (a : G false) :
    dehnTwist φ z (of false a) = of false a :=
  twistHom_of_false φ _ (commute_of_base_of_mem_centralizer z.property) a

/-- The right factor is conjugated by the image of the parameter. -/
@[simp] theorem dehnTwist_of_true
    (z : Subgroup.centralizer (Set.range (φ true))) (b : G true) :
    dehnTwist φ z (of true b) = of true z * of true b * (of true z)⁻¹ :=
  twistHom_of_true φ _ (commute_of_base_of_mem_centralizer z.property) b

/-- The amalgamating group is fixed pointwise. -/
@[simp] theorem dehnTwist_base
    (z : Subgroup.centralizer (Set.range (φ true))) (c : C) :
    dehnTwist φ z (base φ c) = base φ c := by
  rw [← of_apply_eq_base φ false, dehnTwist_of_false]

/-- The parameter one gives the identity twist. -/
@[simp] theorem dehnTwist_one : dehnTwist φ 1 = 1 :=
  MulEquiv.toMonoidHom_injective (rightHom_one φ)

/-- Composition has the same order as multiplication of the parameters in the right factor. -/
@[simp] theorem dehnTwist_mul
    (z w : Subgroup.centralizer (Set.range (φ true))) :
    dehnTwist φ (z * w) = dehnTwist φ z * dehnTwist φ w :=
  MulEquiv.toMonoidHom_injective (rightHom_comp φ z w).symm

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
  exact congrArg K.map (MonoidHom.ext fun a => dehnTwist_of_false φ z a)

/-- Every subgroup of the right factor is carried to its conjugate by the parameter. -/
@[simp] theorem map_dehnTwist_map_of_true
    (z : Subgroup.centralizer (Set.range (φ true))) (K : Subgroup (G true)) :
    (K.map (of (φ := φ) true)).map (dehnTwist φ z : PushoutI φ →* PushoutI φ) =
      (K.map (of true)).map (MulAut.conj (of (φ := φ) true z) : PushoutI φ →* PushoutI φ) := by
  simp only [Subgroup.map_map]
  exact congrArg K.map (MonoidHom.ext fun b => by simp [MulAut.conj_apply])

/-! ### Necessity of the centralizer hypothesis -/

/-- With injective boundary maps, an endomorphism of the amalgamated product that fixes the left
factor and conjugates the right factor by an element `z` of the right factor can only exist when
`z` centralizes the image of the amalgamating group: the prescription sends an amalgamated
element `c` both to `c` and to `z * c * z⁻¹`. -/
theorem mem_centralizer_range_of_map_of_true_eq (hφ : ∀ i, Function.Injective (φ i))
    {z : G true} (f : PushoutI φ →* PushoutI φ) (hfalse : ∀ a, f (of false a) = of false a)
    (htrue : ∀ b, f (of true b) = of true z * of true b * (of true z)⁻¹) :
    z ∈ Subgroup.centralizer (Set.range (φ true)) := by
  rintro _ ⟨c, rfl⟩
  apply of_injective hφ true
  have h : of (φ := φ) true (φ true c) = of true z * of true (φ true c) * (of true z)⁻¹ := by
    rw [← htrue, of_apply_eq_base, ← of_apply_eq_base φ false, hfalse]
  simpa [map_mul] using (mul_inv_eq_iff_eq_mul.mp h.symm).symm

/-- With injective boundary maps, the rule fixing the left factor and conjugating the right
factor by an element `z` of the right factor defines an endomorphism of the amalgamated product
exactly when `z` centralizes the image of the amalgamating group. -/
theorem exists_map_of_true_eq_iff_mem_centralizer (hφ : ∀ i, Function.Injective (φ i))
    {z : G true} :
    (∃ f : PushoutI φ →* PushoutI φ, (∀ a, f (of false a) = of false a) ∧
      ∀ b, f (of true b) = of true z * of true b * (of true z)⁻¹) ↔
      z ∈ Subgroup.centralizer (Set.range (φ true)) :=
  ⟨fun ⟨f, hfalse, htrue⟩ => mem_centralizer_range_of_map_of_true_eq φ hφ f hfalse htrue,
    fun hz => ⟨dehnTwist φ ⟨z, hz⟩, dehnTwist_of_false φ _, dehnTwist_of_true φ _⟩⟩

/-! ### Twisting by a parameter of the fixed factor -/

/-- The endomorphism underlying the twist by a parameter of the left factor. -/
private abbrev leftHom (z : Subgroup.centralizer (Set.range (φ false))) :
    PushoutI φ →* PushoutI φ :=
  twistHom φ (of false (z : G false)) (commute_of_base_of_mem_centralizer z.property)

private theorem leftHom_comp (z w : Subgroup.centralizer (Set.range (φ false))) :
    (leftHom φ z).comp (leftHom φ w) = leftHom φ (w * z) :=
  twistHom_comp φ _ _ _ (by simp [twistHom_of_false])

private theorem leftHom_one : leftHom φ 1 = MonoidHom.id _ := by
  simpa [leftHom] using twistHom_one φ

/-- The twist fixing the left factor and conjugating the right factor by a parameter `z` of the
*left* factor centralizing the left-hand image of the amalgamating group. Since these twists fix
their own parameters, they compose in the order opposite to multiplication of parameters:
see `leftDehnTwist_mul`. -/
def leftDehnTwist (z : Subgroup.centralizer (Set.range (φ false))) : MulAut (PushoutI φ) :=
  MonoidHom.toMulEquiv (leftHom φ z) (leftHom φ z⁻¹)
    (by rw [leftHom_comp, mul_inv_cancel, leftHom_one])
    (by rw [leftHom_comp, inv_mul_cancel, leftHom_one])

/-- The left factor is fixed pointwise. -/
@[simp] theorem leftDehnTwist_of_false
    (z : Subgroup.centralizer (Set.range (φ false))) (a : G false) :
    leftDehnTwist φ z (of false a) = of false a :=
  twistHom_of_false φ _ (commute_of_base_of_mem_centralizer z.property) a

/-- The right factor is conjugated by the image of the parameter in the left factor. -/
@[simp] theorem leftDehnTwist_of_true
    (z : Subgroup.centralizer (Set.range (φ false))) (b : G true) :
    leftDehnTwist φ z (of true b) = of false z * of true b * (of false z)⁻¹ :=
  twistHom_of_true φ _ (commute_of_base_of_mem_centralizer z.property) b

/-- The amalgamating group is fixed pointwise. -/
@[simp] theorem leftDehnTwist_base
    (z : Subgroup.centralizer (Set.range (φ false))) (c : C) :
    leftDehnTwist φ z (base φ c) = base φ c := by
  rw [← of_apply_eq_base φ false, leftDehnTwist_of_false]

/-- The parameter one gives the identity twist. -/
@[simp] theorem leftDehnTwist_one : leftDehnTwist φ 1 = 1 :=
  MulEquiv.toMonoidHom_injective (leftHom_one φ)

/-- Twists by parameters of the left factor compose in the order opposite to multiplication of
the parameters. -/
@[simp] theorem leftDehnTwist_mul (z w : Subgroup.centralizer (Set.range (φ false))) :
    leftDehnTwist φ (z * w) = leftDehnTwist φ w * leftDehnTwist φ z :=
  MulEquiv.toMonoidHom_injective (leftHom_comp φ w z).symm

/-- Inverting the parameter gives the inverse twist. -/
@[simp] theorem leftDehnTwist_inv (z : Subgroup.centralizer (Set.range (φ false))) :
    leftDehnTwist φ z⁻¹ = (leftDehnTwist φ z)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← leftDehnTwist_mul, mul_inv_cancel, leftDehnTwist_one]

/-- Every subgroup of the left factor is fixed. -/
@[simp] theorem map_leftDehnTwist_map_of_false
    (z : Subgroup.centralizer (Set.range (φ false))) (K : Subgroup (G false)) :
    (K.map (of (φ := φ) false)).map (leftDehnTwist φ z : PushoutI φ →* PushoutI φ) =
      K.map (of false) := by
  rw [Subgroup.map_map]
  exact congrArg K.map (MonoidHom.ext fun a => leftDehnTwist_of_false φ z a)

/-- Every subgroup of the right factor is carried to its conjugate by the parameter. -/
@[simp] theorem map_leftDehnTwist_map_of_true
    (z : Subgroup.centralizer (Set.range (φ false))) (K : Subgroup (G true)) :
    (K.map (of (φ := φ) true)).map (leftDehnTwist φ z : PushoutI φ →* PushoutI φ) =
      (K.map (of true)).map (MulAut.conj (of (φ := φ) false z) : PushoutI φ →* PushoutI φ) := by
  simp only [Subgroup.map_map]
  exact congrArg K.map (MonoidHom.ext fun b => by simp [MulAut.conj_apply])

/-- A parameter of the left factor and a parameter of the right factor with the same image in
the amalgamated product define the same twist. This applies to the two images of an element of
the amalgamating group. -/
theorem leftDehnTwist_eq_dehnTwist (z : Subgroup.centralizer (Set.range (φ false)))
    (w : Subgroup.centralizer (Set.range (φ true)))
    (h : of (φ := φ) false (z : G false) = of true (w : G true)) :
    leftDehnTwist φ z = dehnTwist φ w := by
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext_nonempty
  intro i
  ext g
  cases i <;> simp [h]

end Monoid.PushoutI
