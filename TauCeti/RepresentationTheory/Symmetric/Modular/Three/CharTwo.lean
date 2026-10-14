/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Standard
import TauCeti.RepresentationTheory.PGroupInvariants
import TauCeti.GroupTheory.Perm.FinThree.Basic
import TauCeti.RepresentationTheory.Intertwining

/-!
# Simple representations of S₃ in characteristic two

Over every field of characteristic two, an irreducible representation of S₃ is equivalent to
its trivial line or its two-dimensional standard representation. No algebraic closure or
finite-dimensionality hypothesis is needed. These are the simple-module representatives for
the integral composition-multiplicity coordinates of the exact Grothendieck group.

A point stabilizer has order two, so it fixes a nonzero vector in every nonzero representation.
Its orbit gives a nonzero map from the three-point permutation representation, which splits
as the trivial line and the irreducible standard representation.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

namespace TauCeti

open Representation

universe u v

variable {k : Type u} [Field k] [CharP k 2]
  {V : Type v} [AddCommGroup V] [Module k V]

private theorem exists_nonzero_permutation_intertwiner [Nontrivial V]
    (ρ : Representation k (Equiv.Perm (Fin 3)) V) :
    ∃ f : IntertwiningMap (ofMulAction k (Equiv.Perm (Fin 3)) (Fin 3)) ρ, f ≠ 0 := by
  classical
  let H := MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)
  have hpow (g : H) : (ρ.comp H.subtype) g ^ 2 ^ 1 = 1 := by
    have hg : g ^ 2 = 1 := by
      apply Subtype.ext
      rcases (mem_stabilizer_perm_fin_three_iff 0 g).mp g.property with h | h
      · simp [h]
      · simp [h, pow_two, Equiv.swap_mul_self]
    simp only [pow_one, ← map_pow, hg, map_one]
  obtain ⟨v, hv, hfix⟩ :=
    Representation.exists_ne_zero_apply_eq_self_of_forall_pow_eq_one 2
      (ρ.comp H.subtype)
      (fun g ↦ ⟨1, hpow g⟩)
  let w (i : Fin 3) := ρ (Equiv.swap 0 i) v
  have hw (g : Equiv.Perm (Fin 3)) (i : Fin 3) : w (g i) = ρ g (w i) := by
    let h := (Equiv.swap 0 (g i))⁻¹ * g * Equiv.swap 0 i
    have hh : h ∈ H := by
      simp [h, H, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
        Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have hf : ρ h v = v := hfix ⟨h, hh⟩
    have he : g * Equiv.swap 0 i = Equiv.swap 0 (g i) * h := by simp [h, mul_assoc]
    calc
      w (g i) = ρ (Equiv.swap 0 (g i)) (ρ h v) := by rw [hf]
      _ = ρ g (w i) := by simp only [w, ← Module.End.mul_apply, ← map_mul, ← he]
  let L := (MonoidAlgebra.basis (Fin 3) k).constr k w
  have hL (i : Fin 3) (c : k) : L (MonoidAlgebra.single i c) = c • w i := by
    have he : MonoidAlgebra.single i c = c • MonoidAlgebra.basis (Fin 3) k i := by
      simp [MonoidAlgebra.basis_apply]
    rw [he, map_smul]
    exact congrArg (c • ·) ((MonoidAlgebra.basis (Fin 3) k).constr_basis k w i)
  let f : IntertwiningMap (ofMulAction k (Equiv.Perm (Fin 3)) (Fin 3)) ρ :=
    L.intertwiningMap_of_isIntertwiningMap _ _ fun g x ↦ by
      induction x using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp [hx, hy]
      | single i c => simp [ofMulAction_single, hL, Equiv.Perm.smul_def, hw]
  refine ⟨f, fun hf ↦ hv ?_⟩
  have he := DFunLike.congr_fun hf (MonoidAlgebra.single 0 1)
  simpa [f, hL, w, ← Equiv.Perm.one_def] using he

/-- Every irreducible S₃ representation in characteristic two is equivalent to the trivial
line or the standard representation. The coefficient field need not be algebraically closed,
and the representation need not be assumed finite-dimensional. -/
theorem _root_.Representation.IsIrreducible.nonempty_equiv_trivial_or_standard_perm_fin_three
    {ρ : Representation k (Equiv.Perm (Fin 3)) V} (hρ : ρ.IsIrreducible) :
    Nonempty (ρ.Equiv (trivial k (Equiv.Perm (Fin 3)) k)) ∨
      Nonempty (ρ.Equiv (standardRepresentation k (Fin 3))) := by
  classical
  let := hρ
  have := hρ.nontrivial
  have hthree : (3 : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (by decide : Nat.Prime 3) (by decide : 2 ≠ 3)
  have hstd : (standardRepresentation k (Fin 3)).IsIrreducible :=
    isIrreducible_standardRepresentation_fin_three hthree
  have : (augmentationSubrepresentation k (Equiv.Perm (Fin 3))
      (Fin 3)).toRepresentation.IsIrreducible := by
    simpa only [toRepresentation_augmentationSubrepresentation] using hstd
  obtain ⟨f, hf⟩ := exists_nonzero_permutation_intertwiner ρ
  let e := ofMulActionEquivProdAugmentation k (Equiv.Perm (Fin 3)) (Fin 3)
    (isUnit_iff_ne_zero.mpr (by simpa using hthree))
  let F := f.comp e.symm.toIntertwiningMap
  let a := F.comp (IntertwiningMap.inl k _ _)
  let b := F.comp (IntertwiningMap.inr k _ _)
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    -- Composing the zero intertwining map with either inclusion is definitionally zero,
    -- so `h.1` and `h.2` give the two equalities required by `prod_ext`.
    have hF : F = 0 := IntertwiningMap.prod_ext
      h.1 h.2
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hz := DFunLike.congr_fun hF (e x)
    simpa [F] using hz
  rcases hab with ha | hb
  · exact Or.inl ⟨(a.ofBijective ((IsIrreducible.bijective_or_eq_zero a).resolve_right ha)).symm⟩
  · have hbije := (IsIrreducible.bijective_or_eq_zero b).resolve_right hb
    simpa only [toRepresentation_augmentationSubrepresentation] using
      Or.inr (Nonempty.intro (b.ofBijective hbije).symm)

end TauCeti
