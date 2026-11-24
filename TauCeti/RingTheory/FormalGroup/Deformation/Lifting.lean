/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Deformation.Basic
import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial

/-!
# Lifting formal group deformations along surjections

Every commutative formal group law over `B` lifts along a surjective ring homomorphism
`q : A →+* B`, because the Lazard ring is a polynomial ring
(`FormalGroup.exists_map_eq_of_surjective`). Consequently, for any compatible reductions
`π_A : A →+* k` and `π_B : B →+* k` with `π_B.comp q = π_A`, base change along `q` is surjective
on framed lifts (`TauCeti.FormalGroupLift.map_surjective`) and on coordinate-equivalence classes
of deformations (`TauCeti.FormalGroupDeformation.map_surjective`).

## Main results

* `TauCeti.FormalGroupLift.map_surjective`: base change of framed lifts along a surjective ring
  homomorphism is surjective.
* `TauCeti.FormalGroupDeformation.map_surjective`: base change of deformation classes along a
  surjective ring homomorphism is surjective.
* `TauCeti.FormalGroupDeformation.exists_mk_eq_and_map_eq`: replaces a lift whose reduction along
  a coordinate-lifting homomorphism is deformation-equivalent to `F.map q hq` with an equivalent
  lift having literally the same reduction `G.map q hq = F.map q hq`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1–§2.
-/

public section

namespace TauCeti

variable {A B k : Type*} [CommRing A] [CommRing B] [CommRing k]
  {π_A : A →+* k} {π_B : B →+* k} {F₀ : FormalGroup k}

namespace FormalGroupLift

/-- Every commutative formal group lift over `B` lifts along any surjective ring homomorphism
`q : A →+* B` compatible with the reductions to `k`. -/
theorem map_surjective {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) :
    Function.Surjective (fun F : FormalGroupLift π_A F₀ ↦ F.map q hq) := fun G ↦ by
  obtain ⟨H, hH_comm, hHq⟩ := FormalGroup.exists_map_eq_of_surjective G.formalGroup hq_surj
  exact ⟨⟨H, hH_comm, by rw [← hq, ← FormalGroup.map_comp, hHq, G.map_eq]⟩,
    FormalGroupLift.ext (by simpa using hHq)⟩

end FormalGroupLift

namespace FormalGroupDeformation

/-- Base change of formal group deformations along any surjective ring homomorphism is surjective,
by Lazard's theorem that commutative formal group laws lift along surjections. -/
theorem map_surjective {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_surj : Function.Surjective q) :
    Function.Surjective
      (FormalGroupDeformation.map q hq :
        FormalGroupDeformation π_A F₀ → FormalGroupDeformation π_B F₀) := by
  intro y
  induction y using Quotient.inductionOn with | _ G =>
  obtain ⟨F, rfl⟩ := FormalGroupLift.map_surjective hq hq_surj G
  exact ⟨⟦F⟧, map_mk q hq F⟩

/-- Replaces a lift `G₀` whose reduction modulo `q` is deformation-equivalent to `F.map q hq` with
an equivalent lift `G` having literally the same reduction `G.map q hq = F.map q hq`, whenever
formal coordinates lift along `q` (for example, along a surjective local homomorphism or a
surjection with nilpotent kernel). -/
theorem exists_mk_eq_and_map_eq {q : A →+* B} (hq : π_B.comp q = π_A)
    (hq_coord : Function.Surjective (FormalCoordinate.map q))
    {F G₀ : FormalGroupLift π_A F₀}
    (hx : FormalGroupDeformation.map q hq ⟦G₀⟧ = ⟦F.map q hq⟧) :
    ∃ G : FormalGroupLift π_A F₀, (⟦G⟧ : FormalGroupDeformation π_A F₀) = ⟦G₀⟧ ∧
      G.map q hq = F.map q hq := by
  rw [map_mk] at hx
  obtain ⟨ψ, hψ_π, hψ_eq⟩ := (mk_eq_mk_iff _ _).mp hx
  obtain ⟨φ₀, hφ₀_q⟩ := hq_coord ψ
  have hφ₀_π : FormalCoordinate.map π_A φ₀ = 1 := by
    rw [← hq, FormalCoordinate.map_comp, hφ₀_q, hψ_π]
  let φ : (FormalCoordinate.map π_A).ker := ⟨φ₀, MonoidHom.mem_ker.mpr hφ₀_π⟩
  refine ⟨φ • G₀, ((mk_eq_mk_iff G₀ (φ • G₀)).mpr ⟨φ₀, hφ₀_π, rfl⟩).symm,
    FormalGroupLift.ext ?_⟩
  rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_smul, FormalGroup.map_smul,
    hφ₀_q, ← FormalGroupLift.formalGroup_map G₀ q hq, hψ_eq]

end FormalGroupDeformation

end TauCeti
