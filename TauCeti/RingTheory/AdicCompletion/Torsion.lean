/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# The completion action on ideal-power-torsion modules

An `R`-module in which every element is killed by a power of `I` has a canonical action of
`AdicCompletion I R`. On an element killed by `I ^ n`, a completed scalar acts through its
residue modulo `I ^ n`. No finite generation or Noetherian hypothesis is needed.

`AdicCompletion.torsionModule` constructs this module structure. The residue formula
`AdicCompletion.torsionModule_smul_eq` characterizes its action. Every `R`-linear map between
such modules is linear for these completion actions, and restriction of scalars recovers the
original action of `R`.

The construction uses the compatible residues of Mathlib's `AdicCompletion`, formalized by
Judith Ludwig and Christian Merten. For its role in Matlis duality, see the Stacks Project,
Section 47.7, Tag 08Z1.
-/

public section

noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private def representative (a : AdicCompletion I R) (n : ℕ) : R :=
  Quotient.out (a.val n)

private theorem representative_spec (a : AdicCompletion I R) {n m : ℕ} (h : n ≤ m) :
    Submodule.Quotient.mk (representative a m) = a.val n := by
  exact (congrArg (transitionMap I R h) (Quotient.out_eq (a.val m))).trans (a.property h)

private theorem smul_eq_of_residue_eq {x : M} {n : ℕ}
    (hx : ∀ r ∈ I ^ n, r • x = 0) {r s : R}
    (h : (Submodule.Quotient.mk r : R ⧸ (I ^ n • ⊤ : Ideal R)) =
      Submodule.Quotient.mk s) : r • x = s • x := by
  have hmem : r - s ∈ I ^ n := by
    simpa using (Submodule.Quotient.eq _).mp h
  exact sub_eq_zero.mp (by simpa [sub_smul] using hx (r - s) hmem)

variable (hM : ∀ x : M, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)

private def torsionAction (a : AdicCompletion I R) (x : M) : M :=
  representative a (hM x).choose • x

private theorem torsionAction_eq {a : AdicCompletion I R} {x : M} {n : ℕ} {r : R}
    (hx : ∀ s ∈ I ^ n, s • x = 0)
    (ha : a.val n = Submodule.Quotient.mk r) : torsionAction hM a x = r • x := by
  let k := max n (hM x).choose
  have h₁ : representative a (hM x).choose • x = representative a k • x :=
    smul_eq_of_residue_eq (hM x).choose_spec
      ((representative_spec a le_rfl).trans (representative_spec a (Nat.le_max_right _ _)).symm)
  have h₂ : representative a k • x = r • x :=
    smul_eq_of_residue_eq hx ((representative_spec a (Nat.le_max_left _ _)).trans ha)
  exact h₁.trans h₂

private theorem torsionAction_representative (a : AdicCompletion I R) {x : M} {n : ℕ}
    (hx : ∀ r ∈ I ^ n, r • x = 0) :
    torsionAction hM a x = representative a n • x :=
  torsionAction_eq hM hx (representative_spec a le_rfl).symm

/-- The canonical module structure over the completion on a module whose elements are each
annihilated by a power of `I`. Use it with `letI := AdicCompletion.torsionModule hM`. -/
@[instance_reducible]
def torsionModule : Module (AdicCompletion I R) M where
  smul := torsionAction hM
  one_smul x := by
    -- The structure field uses the scalar operation being constructed.
    change torsionAction hM 1 x = x
    obtain ⟨n, hn⟩ := hM x
    simpa using torsionAction_eq hM hn (r := 1) rfl
  mul_smul a b x := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM (a * b) x = torsionAction hM a (torsionAction hM b x)
    obtain ⟨n, hn⟩ := hM x
    have hb : ∀ r ∈ I ^ n, r • torsionAction hM b x = 0 := by
      intro r hr
      rw [torsionAction_representative hM b hn, smul_comm, hn r hr, smul_zero]
    rw [torsionAction_representative hM a hb, torsionAction_representative hM b hn]
    rw [torsionAction_eq hM hn (r := representative a n * representative b n)]
    · exact mul_smul _ _ _
    · rw [val_mul, ← representative_spec a le_rfl, ← representative_spec b le_rfl]
      rfl
  smul_zero a := by
    -- The scalar operation is the action defined above.
    change torsionAction hM a 0 = 0
    simp [torsionAction]
  smul_add a x y := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM a (x + y) = torsionAction hM a x + torsionAction hM a y
    obtain ⟨n, hn⟩ := hM x
    obtain ⟨m, hm⟩ := hM y
    have hx : ∀ r ∈ I ^ (max n m), r • x = 0 :=
      fun r hr ↦ hn r (Ideal.pow_le_pow_right (Nat.le_max_left _ _) hr)
    have hy : ∀ r ∈ I ^ (max n m), r • y = 0 :=
      fun r hr ↦ hm r (Ideal.pow_le_pow_right (Nat.le_max_right _ _) hr)
    have hxy : ∀ r ∈ I ^ (max n m), r • (x + y) = 0 := by
      intro r hr
      simp [smul_add, hx r hr, hy r hr]
    rw [torsionAction_representative hM a hxy, torsionAction_representative hM a hx,
      torsionAction_representative hM a hy, smul_add]
  add_smul a b x := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM (a + b) x = torsionAction hM a x + torsionAction hM b x
    obtain ⟨n, hn⟩ := hM x
    rw [torsionAction_representative hM a hn, torsionAction_representative hM b hn]
    rw [torsionAction_eq hM hn (r := representative a n + representative b n)]
    · exact add_smul _ _ _
    · rw [val_add_apply, ← representative_spec a le_rfl, ← representative_spec b le_rfl]
      rfl
  zero_smul x := by
    -- The structure field uses the scalar operation being constructed.
    change torsionAction hM 0 x = 0
    obtain ⟨n, hn⟩ := hM x
    simpa using torsionAction_eq hM hn (r := 0) rfl

/-- A completed scalar acts on an element killed by `I ^ n` through its residue modulo
`I ^ n`. This formula permits any representative of the residue. -/
theorem torsionModule_smul_eq (a : AdicCompletion I R) (x : M) {n : ℕ} (r : R)
    (hx : ∀ s ∈ I ^ n, s • x = 0)
    (ha : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r) :
    letI := torsionModule hM
    a • x = r • x := by
  apply torsionAction_eq hM hx
  apply (Ideal.quotientEquivAlgOfEq R (show (I ^ n • ⊤ : Ideal R) = I ^ n by simp)).injective
  exact ha

/-- The canonical completion action extends the scalar tower from `R`. -/
instance torsionModule_isScalarTower :
    letI := torsionModule hM
    IsScalarTower R (AdicCompletion I R) M := by
  let := torsionModule hM
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  obtain ⟨n, hn⟩ := hM x
  exact torsionModule_smul_eq hM _ x r hn (evalₐ_of I n r)

end AdicCompletion

namespace LinearMap

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ x : M, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
variable (hN : ∀ y : N, ∃ n : ℕ, ∀ r ∈ I ^ n, r • y = 0)

/-- An `R`-linear map between ideal-power-torsion modules commutes with the canonical
completion actions. -/
@[simp]
theorem map_adicCompletion_smul (f : M →ₗ[R] N) (a : AdicCompletion I R) (x : M) :
    letI := AdicCompletion.torsionModule hM
    letI := AdicCompletion.torsionModule hN
    f (a • x) = a • f x := by
  obtain ⟨n, hn⟩ := hM x
  have hfx : ∀ r ∈ I ^ n, r • f x = 0 := by
    intro r hr
    rw [← f.map_smul, hn r hr, f.map_zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [AdicCompletion.torsionModule_smul_eq hM a x r hn hr.symm,
    AdicCompletion.torsionModule_smul_eq hN a (f x) r hfx hr.symm, f.map_smul]

/-- Restriction of scalars identifies linear maps for the canonical completion actions with
`R`-linear maps between ideal-power-torsion modules. -/
def adicCompletionEquiv :
    letI := AdicCompletion.torsionModule hM
    letI := AdicCompletion.torsionModule hN
    (M →ₗ[AdicCompletion I R] N) ≃ₗ[R] (M →ₗ[R] N) := by
  letI := AdicCompletion.torsionModule hM
  letI := AdicCompletion.torsionModule hN
  exact
    { toFun := fun f ↦ f.restrictScalars R
      invFun := fun f ↦
        { toFun := f
          map_add' := f.map_add
          map_smul' := f.map_adicCompletion_smul hM hN }
      left_inv := fun f ↦ by ext; rfl
      right_inv := fun f ↦ by ext; rfl
      map_add' := fun f g ↦ by ext; rfl
      map_smul' := fun r f ↦ by ext; rfl }

/-- The comparison of Hom modules is restriction of scalars. -/
@[simp]
theorem adicCompletionEquiv_apply
    (f : letI := AdicCompletion.torsionModule hM
         letI := AdicCompletion.torsionModule hN
         M →ₗ[AdicCompletion I R] N) (x : M) :
    adicCompletionEquiv hM hN f x = f x := (rfl)

/-- Extending a linear map to the canonical completion actions preserves its values. -/
@[simp]
theorem adicCompletionEquiv_symm_apply (f : M →ₗ[R] N) (x : M) :
    (adicCompletionEquiv hM hN).symm f x = f x := (rfl)

end LinearMap
