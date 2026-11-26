/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Twisted conjugacy classes

For a group endomorphism `σ`, twisted conjugation is the action `g • b = g b σ(g)⁻¹`.
The orbit quotient admits descent of invariant functions and is functorial in homomorphisms
that commute with the endomorphisms. For arithmetic Frobenius on the coefficient points of a
reductive group, this is the construction of Kottwitz's set `B(G)`.

## References

* R. E. Kottwitz, *Isocrystals with additional structure*, Compositio Math. 56 (1985), p. 202.
-/

public section

namespace TauCeti

variable {G H J : Type*} [Group G] [Group H] [Group J]

/-- The elements of `G` with the action by `σ`-twisted conjugation. -/
@[ext]
structure TwistedConj (σ : G →* G) where
  /-- The underlying group element. -/
  val : G

namespace TwistedConj

variable {σ : G →* G} {τ : H →* H} {υ : J →* J}

instance : MulAction G (TwistedConj σ) where
  smul g b := ⟨g * b.val * (σ g)⁻¹⟩
  one_smul := fun ⟨b⟩ => congrArg (TwistedConj.mk (σ := σ)) (by simp)
  mul_smul g h := fun ⟨b⟩ =>
    let eq : (g * h) * b * (σ (g * h))⁻¹ = g * (h * b * (σ h)⁻¹) * (σ g)⁻¹ := by
      simp [mul_assoc]
    congrArg (TwistedConj.mk (σ := σ)) eq

@[simp]
theorem val_smul (g : G) (b : TwistedConj σ) :
    (g • b).val = g * b.val * (σ g)⁻¹ := (rfl)

/-- Two representatives are in the same orbit precisely when a twisted conjugator takes
the first to the second. -/
theorem orbitRel_iff {b c : TwistedConj σ} :
    MulAction.orbitRel G (TwistedConj σ) b c ↔ ∃ g : G, c.val = g * b.val * (σ g)⁻¹ := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm, MulAction.mem_orbit_iff]
  exact exists_congr fun g =>
    ⟨fun h => (congrArg TwistedConj.val h.symm).trans (val_smul g b),
      fun h => TwistedConj.ext ((val_smul g b).trans h.symm)⟩

/-- Stabilizing `b` is the twisted commutation equation. -/
@[simp high]
theorem mem_stabilizer_iff {g : G} {b : TwistedConj σ} :
    g ∈ MulAction.stabilizer G b ↔ g * b.val = b.val * σ g := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact mul_inv_eq_iff_eq_mul.mp ((val_smul g b).symm.trans (congrArg TwistedConj.val h))
  · intro h
    exact TwistedConj.ext ((val_smul g b).trans (mul_inv_eq_iff_eq_mul.mpr h))

/-- The set of `σ`-twisted conjugacy classes. -/
abbrev Classes (σ : G →* G) := MulAction.orbitRel.Quotient G (TwistedConj σ)

namespace Classes

/-- The twisted conjugacy class of a representative. -/
def mk (σ : G →* G) (b : G) : Classes σ := Quotient.mk _ ⟨b⟩

theorem mk_surjective (σ : G →* G) : Function.Surjective (mk σ) := by
  intro q
  obtain ⟨⟨b⟩, rfl⟩ := Quotient.exists_rep q
  exact ⟨b, rfl⟩

theorem mk_eq_mk_iff {b c : G} :
    mk σ b = mk σ c ↔ ∃ g : G, c = g * b * (σ g)⁻¹ :=
  Quotient.eq.trans orbitRel_iff

@[simp]
theorem mk_twistedConj (g b : G) : mk σ (g * b * (σ g)⁻¹) = mk σ b :=
  MulAction.orbitRel.Quotient.quotient_smul_eq (g := g) (a := (⟨b⟩ : TwistedConj σ))

/-- An invariant function descends to twisted conjugacy classes. -/
def lift {X : Sort*} (f : G → X) (hf : ∀ g b, f (g * b * (σ g)⁻¹) = f b) : Classes σ → X :=
  Quotient.lift (fun b => f b.val) fun _ _ h => by
    obtain ⟨g, hg⟩ := orbitRel_iff.mp h
    rw [hg, hf]

@[simp]
theorem lift_mk {X : Sort*} (f : G → X) (hf : ∀ g b, f (g * b * (σ g)⁻¹) = f b) (b : G) :
    lift (σ := σ) f hf (mk σ b) = f b := (rfl)

/-- Functions on twisted conjugacy classes are determined by their values on representatives. -/
theorem ext {X : Sort*} {f h : Classes σ → X} (heq : ∀ b, f (mk σ b) = h (mk σ b)) : f = h :=
  _root_.funext <| (mk_surjective σ).forall.mpr heq

/-- A homomorphism commuting with the two endomorphisms induces a function on classes. -/
def map (f : G →* H) (hf : Function.Semiconj f σ τ) : Classes σ → Classes τ :=
  lift (fun b => mk τ (f b)) fun g b => by simp [hf g]

@[simp]
theorem map_mk (f : G →* H) (hf : Function.Semiconj f σ τ) (b : G) :
    map f hf (mk σ b) = mk τ (f b) := (rfl)

@[simp]
theorem map_id : map (MonoidHom.id G) (fun _ => rfl : Function.Semiconj (id : G → G) σ σ) = id :=
  ext fun _ => rfl

theorem map_comp (f : G →* H) (h : H →* J)
    (hf : Function.Semiconj f σ τ) (hh : Function.Semiconj h τ υ) :
    map (h.comp f) (fun x => (congrArg h (hf x)).trans (hh (f x))) = map h hh ∘ map f hf :=
  ext fun _ => rfl

/-- A group equivalence commuting with the endomorphisms induces an equivalence on classes. -/
def congr (e : G ≃* H) (he : Function.Semiconj e σ τ) : Classes σ ≃ Classes τ where
  toFun := map e.toMonoidHom he
  invFun := map e.symm.toMonoidHom fun c => e.injective <| by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using (he (e.symm c)).symm
  left_inv := (mk_surjective σ).forall.mpr fun b => by simp
  right_inv := (mk_surjective τ).forall.mpr fun c => by simp

@[simp]
theorem congr_mk (e : G ≃* H) (he : Function.Semiconj e σ τ) (b : G) :
    congr e he (mk σ b) = mk τ (e b) := (rfl)

@[simp]
theorem congr_symm_mk (e : G ≃* H) (he : Function.Semiconj e σ τ) (c : H) :
    (congr e he).symm (mk τ c) = mk σ (e.symm c) := (rfl)

end Classes
end TwistedConj
end TauCeti
