/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup

/-!
# Reduction of double-coset stabilizers

Consider a class `Γ g K` in `Γ \ G / K`. In level coordinates its stabilizer is
`K ∩ g⁻¹ Γ g`. A local projection need not be faithful on the ambient group `G`:
faithfulness on `Γ` suffices to detect elements of this stabilizer. If the projection
on `K` factors through an integral group, reduction from that group is faithful on
the stabilizer whenever the latter is torsion and the reduction kernel is torsion-free.
-/

public section

namespace TauCeti

variable {G A B C : Type*} [Group G] [Group A] [Group B] [Group C]
  {Γ K : Subgroup G} {g : G}

/-- Reduction is injective on a torsion double-coset stabilizer if the local projection is
injective on the left subgroup and the integral reduction kernel is torsion-free. The
stabilizer here is read inside the level `K`, not inside `Γ`. -/
theorem injective_comp_mackeyToK_of_isMulTorsionFree_ker
    {π : G →* A} (hπ : Set.InjOn π Γ) {j : B →* A} {ρ : K →* B}
    (hρ : j.comp ρ = π.domRestrict K) (r : B →* C) [IsMulTorsionFree r.ker]
    (hS : IsMulTorsion (mackeySubgroup g⁻¹ Γ K)) :
    Function.Injective (r.comp (ρ.comp (mackeyToK g⁻¹ Γ K))) := by
  let f := ρ.comp (mackeyToK g⁻¹ Γ K)
  have hfπ (s : mackeySubgroup g⁻¹ Γ K) : j (f s) = π s := by
    simpa [f] using DFunLike.congr_fun hρ (mackeyToK g⁻¹ Γ K s)
  have hf : Function.Injective f := by
    intro s t hst
    have hs : g * s * g⁻¹ ∈ Γ := by simpa using (mem_mackeySubgroup_iff.mp s.property).2
    have ht : g * t * g⁻¹ ∈ Γ := by simpa using (mem_mackeySubgroup_iff.mp t.property).2
    have he : π (g * s * g⁻¹) = π (g * t * g⁻¹) := by
      simp only [map_mul, ← hfπ s, ← hfπ t, hst]
    exact Subtype.ext ((MulAut.conj g).injective (hπ hs ht he))
  have htorsion : IsMulTorsion f.range := by
    rintro ⟨_, s, rfl⟩
    exact Submonoid.isOfFinOrder_coe.mp (f.isOfFinOrder (hS s))
  let f' := f.codRestrict f.range fun s ↦ ⟨s, rfl⟩
  exact (r.injective_domRestrict_of_isMulTorsion htorsion).comp
    (fun _ _ h ↦ hf (congrArg Subtype.val h) : Function.Injective f')

end TauCeti
