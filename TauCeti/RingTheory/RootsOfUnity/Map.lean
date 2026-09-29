/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RootsOfUnity.PPower

/-!
# Maps on groups of `p`-power roots of unity

A monoid homomorphism restricts to a homomorphism on the groups of `p`-power roots of unity.
These maps preserve identity and composition; a monoid isomorphism yields a group isomorphism.
-/

public section

namespace TauCeti

variable (p : ℕ)
variable {K L : Type*} [CommMonoid K] [CommMonoid L]

/-- The map on `p`-power roots of unity induced by a monoid homomorphism. -/
def pPowerRootsOfUnityMap (f : K →* L) :
    pPowerRootsOfUnity p K →* pPowerRootsOfUnity p L :=
  MonoidHom.codRestrict
    ((Units.map f).comp (pPowerRootsOfUnity p K).subtype)
    (pPowerRootsOfUnity p L) (by
      intro x
      obtain ⟨n, hn⟩ := (mem_pPowerRootsOfUnity_iff p K x).mp x.property
      exact (mem_pPowerRootsOfUnity_iff p L _).mpr
        ⟨n, by
          calc
            (Units.map f (x : Kˣ)) ^ p ^ n =
                Units.map f ((x : Kˣ) ^ p ^ n) := (map_pow _ _ _).symm
            _ = 1 := by rw [hn, map_one]⟩)

/-- The induced map is the usual map on units. -/
@[simp] theorem pPowerRootsOfUnityMap_apply (f : K →* L)
    (x : pPowerRootsOfUnity p K) :
    (pPowerRootsOfUnityMap p f x : Lˣ) = Units.map f x := by
  simp [pPowerRootsOfUnityMap]

/-- Injective monoid homomorphisms induce injective maps on `p`-power roots of unity. -/
theorem pPowerRootsOfUnityMap_injective (f : K →* L)
    (hf : Function.Injective f) :
    Function.Injective (pPowerRootsOfUnityMap p f) := by
  intro x y h
  apply Subtype.ext
  exact Units.map_injective hf (congrArg Subtype.val h)

/-- The identity monoid map acts trivially on the `p`-power roots. -/
@[simp] theorem pPowerRootsOfUnityMap_id :
    pPowerRootsOfUnityMap p (MonoidHom.id K) = MonoidHom.id _ := by
  ext x
  simp

/-- Root-group maps compose as the underlying monoid maps do. -/
@[simp] theorem pPowerRootsOfUnityMap_comp {M : Type*} [CommMonoid M]
    (f : K →* L) (g : L →* M) :
    pPowerRootsOfUnityMap p (g.comp f) =
      (pPowerRootsOfUnityMap p g).comp (pPowerRootsOfUnityMap p f) := by
  ext x
  simp

/-- A monoid isomorphism identifies its two groups of `p`-power roots of unity. -/
noncomputable def pPowerRootsOfUnityEquiv (f : K ≃* L) :
    pPowerRootsOfUnity p K ≃* pPowerRootsOfUnity p L :=
  MulEquiv.ofBijective (pPowerRootsOfUnityMap p f.toMonoidHom) ⟨
    pPowerRootsOfUnityMap_injective p f.toMonoidHom f.injective,
    by
      intro x
      refine ⟨pPowerRootsOfUnityMap p f.symm.toMonoidHom x, ?_⟩
      apply Subtype.ext
      apply Units.ext
      simp⟩

/-- The group isomorphism acts by the given monoid isomorphism on units. -/
@[simp] theorem pPowerRootsOfUnityEquiv_apply (f : K ≃* L)
    (x : pPowerRootsOfUnity p K) :
    (pPowerRootsOfUnityEquiv p f x : Lˣ) = Units.map f.toMonoidHom x := by
  exact pPowerRootsOfUnityMap_apply p f.toMonoidHom x

end TauCeti
