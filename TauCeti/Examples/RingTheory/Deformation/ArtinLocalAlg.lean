/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ZMod.LocalRing
public import TauCeti.RingTheory.Deformation.ArtinLocalAlg
public import TauCeti.RingTheory.Polynomial.Truncated.Basic

/-!
# Checks for the Artinian coefficient category

The rings `ℤ ⧸ p ^ (n + 1)`, reduced modulo `p`, are objects of the Artinian coefficient category
over `ℤ` with residue field `𝔽_p`, so its objects need not be algebras over a field. The truncated
polynomial ring `k[x] ⧸ (x ^ 3)` is an object over `k` whose augmentation is not a small extension:
its kernel `(x)` is principal and nonzero, but is not killed by the maximal ideal, as `x ^ 2 ≠ 0`.
The dual numbers, by contrast, give a small extension (`isSmallExtension_toResidue_dualNumbers`).
The fibre product `k[ε] ×_k k[ε]` exists, as `k[ε] → k` is surjective.
-/

public section

open CategoryTheory IsLocalRing Polynomial

namespace TauCeti.Examples

open Deformation ArtinLocalAlg

/-- `ℤ ⧸ p ^ (n + 1)` with its reduction modulo `p` is an object of `C_ℤ` with residue field
`𝔽_p`. -/
example (p n : ℕ) [Fact p.Prime] :
    IsArtinLocalAug ℤ (ZMod p)
      (Over.mk (CommAlgCat.ofHom
        (ZMod.castHom (dvd_pow_self p n.succ_ne_zero) (ZMod p)).toIntAlgHom)) :=
  ⟨(isArtinian_of_finite : IsArtinianRing (ZMod (p ^ (n + 1)))),
    (inferInstance : IsLocalRing (ZMod (p ^ (n + 1)))), ZMod.ringHom_surjective _⟩

/-- `k[x] ⧸ (x ^ 3)` is an Artinian ring, being finite over `k`. -/
theorem isArtinianRing_cube (k : Type*) [Field k] :
    IsArtinianRing (AdjoinRoot (X ^ 3 : k[X])) :=
  have := (monic_X_pow 3).finite_adjoinRoot (R := k)
  .of_finite k _

attribute [local instance] isArtinianRing_cube

/-- The truncated polynomial ring `k[x] ⧸ (x ^ 3)`, augmented by `x ↦ 0`, as an object of `C_k`. -/
-- Exposed because the carrier of `cube k` is `k[x] ⧸ (x ^ 3)` by definitional unfolding.
@[expose] noncomputable def cube (k : Type*) [Field k] : ArtinLocalAlg k k :=
  mk' (AdjoinRoot (X ^ 3 : k[X])) (AdjoinRoot.liftAlgHom _ (AlgHom.id k k) 0 (by simp))
    fun c ↦ ⟨AdjoinRoot.of _ c, by simp⟩

/-- The augmentation `k[x] ⧸ (x ^ 3) → k` is not a small extension. Its kernel `(x)` is principal
and nonzero, but `x · x ≠ 0` with `x` in the maximal ideal. -/
example (k : Type*) [Field k] : ¬ IsSmallExtension (toResidue (cube k)) := by
  intro h
  -- The class `x` of the variable has `x ^ 2 ≠ 0`, since `x ^ 3` does not divide `x ^ 2`.
  have hsq : AdjoinRoot.root (X ^ 3 : k[X]) * AdjoinRoot.root (X ^ 3 : k[X]) ≠ 0 := by
    rw [← pow_two, ← AdjoinRoot.mk_X, ← map_pow, Ne, AdjoinRoot.mk_eq_zero]
    intro hdvd
    simpa using natDegree_le_of_dvd hdvd (pow_ne_zero 2 X_ne_zero)
  -- The same element, as an element of the object `cube k`.
  set x : (cube k).obj.left := AdjoinRoot.root (X ^ 3 : k[X])
  have hx : (cube k).augmentation x = 0 :=
    (DFunLike.congr_fun (augmentation_mk' (AdjoinRoot (X ^ 3 : k[X])) _ _) x).trans
      (AdjoinRoot.liftAlgHom_root _ _ _ _)
  have hker : x ∈ RingHom.ker (toResidue (cube k)).hom.left.hom := by
    rw [RingHom.mem_ker, toResidue_hom_left_hom]
    exact hx
  have hbot := h.maximalIdeal_mul_ker ▸ Ideal.mul_mem_mul (augmentation_eq_zero_iff.mp hx) hker
  exact hsq (Ideal.mem_bot.mp hbot)

/-- The fibre product `k[ε] ×_k k[ε]` is an object of `C_Λ`. -/
noncomputable example (Λ k : Type*) [CommRing Λ] [Field k] [Algebra Λ k] : ArtinLocalAlg Λ k :=
  pullback (toResidue (dualNumbers Λ k)) (toResidue (dualNumbers Λ k))
    (toResidue_surjective (dualNumbers Λ k))

end TauCeti.Examples
