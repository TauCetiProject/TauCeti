/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Hexacode.Basic
public import TauCeti.InformationTheory.Coding.Semilinear.Aut

/-!
# A semilinear automorphism of the hexacode

Coordinatewise Frobenius carries the hexacode `H` with root `ω` onto the conjugate hexacode with
root `ω²`, and the coordinate ordering `(1,2,4,6,3,5)` carries the conjugate code back to `H`.
The composite is therefore a semilinear automorphism of `H`. It is not a monomial automorphism:
no `F`-linear automorphism of the word space induces it, because Frobenius moves `ω`. So the
semilinear automorphism group of the hexacode is strictly larger than the image of its monomial
automorphism group (`TauCeti.Hexacode.map_monomialAut_code_lt_semilinearAut_code`).

The construction follows Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.7 and
Example 1.3.4.
-/

public section

namespace TauCeti.Hexacode

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

include hω

/-- Coordinatewise Frobenius followed by the coordinate ordering `(1,2,4,6,3,5)` is a semilinear
automorphism of the hexacode. -/
theorem semilinearMonomialEquiv_frobeniusEquiv_conjugatePerm_mem_semilinearAut :
    (semilinearMonomialEquiv 1 conjugatePerm.symm (frobeniusEquiv F 2)).toEquiv ∈
      semilinearAut (code ω) := by
  rw [semilinearMonomialEquiv_toEquiv_mem_semilinearAut_iff]
  ext y
  rw [Submodule.mem_map_equiv, ← mem_code_sq_iff ω, ← map_code_sq_conjugatePerm hω,
    Submodule.mem_map_equiv, LinearEquiv.funCongrLeft_symm]
  refine Iff.of_eq (congrArg (· ∈ code (ω ^ 2)) (funext fun i ↦ ?_))
  simp [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]

/-- The semilinear automorphism of the hexacode given by coordinatewise Frobenius and the
coordinate ordering `(1,2,4,6,3,5)` is not induced by any monomial automorphism. -/
theorem semilinearMonomialEquiv_frobeniusEquiv_conjugatePerm_not_mem_map_monomialAut :
    (semilinearMonomialEquiv 1 conjugatePerm.symm (frobeniusEquiv F 2)).toEquiv ∉
      (monomialAut (code ω)).map
        (MulAction.toPermHom ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) (Fin 6 → F)) := by
  refine semilinearMonomialEquiv_toEquiv_not_mem_map_of_ne_refl _ _ (fun h ↦ ?_) _
  -- Frobenius fixes `ω` only if `ω² = ω`, which contradicts `ω² + ω + 1 = 0` in characteristic two.
  have hfix : ω ^ 2 = ω := by simpa [frobenius_def] using RingEquiv.congr_fun h ω
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  grind

/-- The semilinear automorphism group of the hexacode strictly contains the image of its monomial
automorphism group in the permutation group of the word space. -/
theorem map_monomialAut_code_lt_semilinearAut_code :
    (monomialAut (code ω)).map
        (MulAction.toPermHom ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) (Fin 6 → F)) <
      semilinearAut (code ω) :=
  SetLike.lt_iff_le_and_exists.mpr ⟨map_monomialAut_le_semilinearAut,
    _, semilinearMonomialEquiv_frobeniusEquiv_conjugatePerm_mem_semilinearAut hω,
    semilinearMonomialEquiv_frobeniusEquiv_conjugatePerm_not_mem_map_monomialAut hω⟩

end TauCeti.Hexacode
