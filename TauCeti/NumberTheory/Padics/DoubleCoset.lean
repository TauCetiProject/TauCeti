/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Reduction
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceKernel

/-!
# Double-coset stabilizers at a split prime

For a finite-adelic matrix group, a place with completion `ℚ_[p]` gives a projection to
`GL n ℚ_[p]` that is faithful on the rational points. On an integral level this projection
factors through `GL n ℤ_[p]`. At an odd prime, one such factor suffices to bound the order
of each finite class stabilizer by divisibility and to show that levels reducing to the
identity have trivial stabilizers. These facts remove stabilizer denominators from class
sums at principal level.

The class-stabilizer conclusions correspond to `New.Data.classAut_eq_bot_of_le_levelOf_chosenPlace`
and `New.Data.card_classAut_dvd_chosenGroupOrder` in `New/UpperBound/Objects/LiftChains.lean`
of lsernau/grh-lean, revision `72fead1`. The local argument uses Serre's congruence lemma
instead of bounding characteristic polynomial coefficients at the infinite places.
-/

public section

namespace TauCeti

open Matrix (GeneralLinearGroup)
open Matrix.GeneralLinearGroup (map isMulTorsionFree_ker_map_toZMod)

variable {G n : Type*} [Group G] [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]
  {Γ K : Subgroup G} {g : G}

/-- A finite class stabilizer has order dividing `|GL n (ZMod p)|` if its integral level
admits a projection to `GL n ℤ_[p]` compatible with a projection to `GL n ℚ_[p]` that is
faithful on the left subgroup `Γ`. -/
theorem natCard_mackeySubgroup_dvd_card_GL_zmod (hp : Odd p)
    (π : G →* GL n ℚ_[p]) (hπ : Set.InjOn π Γ) (ρ : K →* GL n ℤ_[p])
    (hρ : (map (algebraMap ℤ_[p] ℚ_[p])).comp ρ = π.domRestrict K)
    (hS : IsMulTorsion (mackeySubgroup g⁻¹ Γ K)) :
    Nat.card (mackeySubgroup g K Γ) ∣ Nat.card (GL n (ZMod p)) := by
  have := isMulTorsionFree_ker_map_toZMod (n := n) hp
  have hinj := injective_comp_mackeyToK_of_isMulTorsionFree_ker hπ hρ (map PadicInt.toZMod) hS
  rw [← natCard_mackeySubgroup_inv_subgroupOf Γ K g,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe mackeySubgroup_le_right).toEquiv]
  exact Subgroup.card_dvd_of_injective _ hinj

/-- A sublevel `J ≤ K` reducing to the identity at one odd prime has trivial class stabilizers.
The local field projection must be faithful on `Γ`, and the stabilizer at the integral
level `K` must be torsion. -/
theorem mackeySubgroup_eq_bot_of_padic_reduction (hp : Odd p)
    {J : Subgroup G} (hle : J ≤ K) (π : G →* GL n ℚ_[p]) (hπ : Set.InjOn π Γ)
    (ρ : K →* GL n ℤ_[p]) (hρ : (map (algebraMap ℤ_[p] ℚ_[p])).comp ρ = π.domRestrict K)
    (hS : IsMulTorsion (mackeySubgroup g⁻¹ Γ K))
    (hred : J.subgroupOf K ≤ ((map PadicInt.toZMod).comp ρ).ker) :
    mackeySubgroup g J Γ = ⊥ := by
  have := isMulTorsionFree_ker_map_toZMod (n := n) hp
  have hinj := injective_comp_mackeyToK_of_isMulTorsionFree_ker hπ hρ (map PadicInt.toZMod) hS
  refine le_bot_iff.mp fun s hs ↦ Subgroup.mem_bot.mpr ?_
  obtain ⟨hsΓ, hsJ⟩ := mem_mackeySubgroup_iff.mp hs
  have hs' : g⁻¹ * s * g ∈ mackeySubgroup g⁻¹ Γ K :=
    mem_mackeySubgroup_iff.mpr ⟨hle hsJ, by simpa [mul_assoc] using hsΓ⟩
  let t : mackeySubgroup g⁻¹ Γ K := ⟨g⁻¹ * s * g, hs'⟩
  have ht : mackeyToK g⁻¹ Γ K t ∈ J.subgroupOf K := by
    simpa only [Subgroup.mem_subgroupOf, coe_mackeyToK_apply, t] using hsJ
  have he : t = 1 := hinj (by
    rw [map_one]
    exact MonoidHom.mem_ker.mp (hred ht))
  exact (MulAut.conj g⁻¹).injective (by simpa [t] using congrArg Subtype.val he)

end TauCeti
