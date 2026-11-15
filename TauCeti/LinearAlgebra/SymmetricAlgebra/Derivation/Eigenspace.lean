/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.OfEnd
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# Integral weight decompositions of a symmetric algebra

Let `f` be an endomorphism of a vector space `M` over a field `K` whose eigenspaces at the integers
span `M`, so `M = ⨁ⱼ M(j)` with `f` acting on `M(j)` by `j`. The derivation `D_f` of the symmetric
algebra `S(M)` extending `f` (`SymmetricAlgebra.derivationOfEnd`) is then diagonalizable with
integer eigenvalues as well: a monomial in eigenvectors of weights `j₁, …, jₙ` is an eigenvector of
`D_f` of weight `j₁ + ⋯ + jₙ`, by the Leibniz rule.

These weights are the characters of the torus action that the grading induces. If `g` is an
endomorphism of `M` acting on each `M(j)` by `cʲ` for a unit `c`, then the algebra endomorphism
`SymmetricAlgebra.map g` of `S(M)` acts on the weight-`w` eigenspace of `D_f` by `cʷ`. In
characteristic zero the integer eigenspaces of `D_f` are independent, so this holds for *every*
eigenvector of `D_f` of weight `w`, not merely for the monomials. In particular every element of
`S(M)` killed by `D_f` is fixed by `map g`. This is the multiplicative counterpart of
`SymmetricAlgebra.map_exp_apply_of_derivationOfEnd_eq_zero`, where `f` is nilpotent and `g` is its
exponential; here `f` is semisimple and `g` ranges over the cocharacter it integrates to, and no
exponential is available over a general field.

For the coadjoint action of an integral semisimple element `h` of a Lie algebra `L` on the
polynomial functions `S(L*)`, this shows that the polynomial functions killed by `h` are invariant
under the grading automorphisms of `L` defined by `h`.

## Main results

* `SymmetricAlgebra.iSup_eigenspace_derivationOfEnd_eq_top`: if the integer eigenspaces of `f`
  span `M`, then the integer eigenspaces of `D_f` span `S(M)`.
* `SymmetricAlgebra.map_apply_of_derivationOfEnd_eq_smul`: if moreover `g` acts on `M(j)` by
  `cʲ`, then `map g` acts on every eigenvector of `D_f` of integer weight `w` by `cʷ`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §16, for the weight decomposition of a
  torus representation and the induced decomposition of its symmetric algebra.
-/

public section

namespace SymmetricAlgebra

open Module

universe u v

variable {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]

/-- The elements of `S(M)` of weight `w` for `D_f`, on which `map g` acts by `c ^ w`. -/
private noncomputable def weightSubmodule (f g : End K M) (c : Kˣ) (w : ℤ) :
    Submodule K (SymmetricAlgebra K M) :=
  End.eigenspace (derivationOfEnd K M f : End K (SymmetricAlgebra K M)) (w : K) ⊓
    End.eigenspace (map K g).toLinearMap ((c ^ w : Kˣ) : K)

private theorem mem_weightSubmodule {f g : End K M} {c : Kˣ} {w : ℤ}
    {p : SymmetricAlgebra K M} :
    p ∈ weightSubmodule f g c w ↔
      derivationOfEnd K M f p = (w : K) • p ∧ map K g p = ((c ^ w : Kˣ) : K) • p := by
  simp [weightSubmodule]

/-- Weights add under multiplication. -/
private theorem mul_mem_weightSubmodule {f g : End K M} {c : Kˣ} {a b : ℤ}
    {p q : SymmetricAlgebra K M} (hp : p ∈ weightSubmodule f g c a)
    (hq : q ∈ weightSubmodule f g c b) : p * q ∈ weightSubmodule f g c (a + b) := by
  rw [mem_weightSubmodule] at hp hq ⊢
  refine ⟨?_, ?_⟩
  · rw [Derivation.leibniz, hp.1, hq.1, smul_eq_mul, smul_eq_mul, mul_smul_comm, mul_smul_comm,
      mul_comm q p, Int.cast_add, add_smul, add_comm]
  · rw [map_mul, hp.2, hq.2, zpow_add, Units.val_mul, smul_mul_smul_comm, mul_comm]

/-- If `f` has integer eigenspaces spanning `M` and `g` acts on `M(j)` by `c ^ j`, then the
joint weight spaces of `D_f` and `map g` span `S(M)`. -/
private theorem iSup_weightSubmodule_eq_top {f g : End K M}
    (hf : ⨆ j : ℤ, f.eigenspace (j : K) = ⊤) {c : Kˣ}
    (hg : ∀ (j : ℤ), ∀ m ∈ f.eigenspace (j : K), g m = ((c ^ j : Kˣ) : K) • m) :
    ⨆ w : ℤ, weightSubmodule f g c w = ⊤ := by
  set W := ⨆ w : ℤ, weightSubmodule f g c w
  -- `W` is closed under multiplication, because the weight spaces multiply.
  have hmul {p q : SymmetricAlgebra K M} (hp : p ∈ W) (hq : q ∈ W) : p * q ∈ W := by
    refine Submodule.iSup_induction _ (motive := fun p ↦ p * q ∈ W) hp (fun a p hp ↦ ?_)
      (by simp) fun p₁ p₂ h₁ h₂ ↦ by rw [add_mul]; exact W.add_mem h₁ h₂
    refine Submodule.iSup_induction _ (motive := fun q ↦ p * q ∈ W) hq (fun b q hq ↦ ?_)
      (by simp) fun q₁ q₂ h₁ h₂ ↦ by rw [mul_add]; exact W.add_mem h₁ h₂
    exact Submodule.mem_iSup_of_mem (a + b) (mul_mem_weightSubmodule hp hq)
  refine eq_top_iff.2 ?_
  rintro p -
  induction p using SymmetricAlgebra.induction with
  | algebraMap r =>
    refine Submodule.mem_iSup_of_mem 0 (mem_weightSubmodule.2 ⟨?_, ?_⟩) <;> simp
  | ι x =>
    -- The generators of the eigenvectors of `f` are joint weight vectors.
    refine Submodule.iSup_induction _ (motive := fun x ↦ ι K M x ∈ W) (hf ▸ Submodule.mem_top)
      (fun j x hx ↦ Submodule.mem_iSup_of_mem j (mem_weightSubmodule.2 ⟨?_, ?_⟩)) (by simp)
      fun x₁ x₂ h₁ h₂ ↦ by rw [map_add]; exact W.add_mem h₁ h₂
    · rw [derivationOfEnd_ι, End.mem_eigenspace_iff.1 hx, map_smul]
    · rw [map_apply_ι, hg j x hx, map_smul]
  | mul p q hp hq => exact hmul hp hq
  | add p q hp hq => exact W.add_mem hp hq

/-- **The induced derivation of an integrally diagonalizable endomorphism is integrally
diagonalizable.** If the eigenspaces of `f` at the integers span `M`, then the eigenspaces at the
integers of the derivation `D_f` of `S(M)` extending `f` span `S(M)`. -/
theorem iSup_eigenspace_derivationOfEnd_eq_top {f : End K M}
    (hf : ⨆ j : ℤ, f.eigenspace (j : K) = ⊤) :
    ⨆ w : ℤ, End.eigenspace (derivationOfEnd K M f : End K (SymmetricAlgebra K M)) (w : K) = ⊤ :=
  -- Take `g = id` and `c = 1` in the joint weight decomposition.
  eq_top_iff.2 <| (iSup_weightSubmodule_eq_top hf (g := LinearMap.id) (c := 1)
    fun j m _ ↦ by simp).ge.trans <| iSup_mono fun _ ↦ inf_le_left

/-- **The torus attached to an integral weight decomposition acts on weight vectors by
characters.** Suppose the eigenspaces `M(j)` of `f` at the integers span `M`, and `g` acts on each
`M(j)` by `c ^ j` for a unit `c`. Then the algebra map `map g` of `S(M)` acts by `c ^ w` on every
eigenvector of weight `w` of the derivation `D_f` extending `f`. -/
theorem map_apply_of_derivationOfEnd_eq_smul [CharZero K] {f g : End K M}
    (hf : ⨆ j : ℤ, f.eigenspace (j : K) = ⊤) {c : Kˣ}
    (hg : ∀ (j : ℤ), ∀ m ∈ f.eigenspace (j : K), g m = ((c ^ j : Kˣ) : K) • m) {w : ℤ}
    {p : SymmetricAlgebra K M} (hp : derivationOfEnd K M f p = (w : K) • p) :
    map K g p = ((c ^ w : Kˣ) : K) • p := by
  set D := (derivationOfEnd K M f : End K (SymmetricAlgebra K M))
  -- Split `p` as `a + b` with `a` of weight `w` and `b` a sum of joint weight vectors of
  -- other weights.
  have hpW : p ∈ ⨆ v : ℤ, weightSubmodule f g c v := by
    rw [iSup_weightSubmodule_eq_top hf hg]
    exact Submodule.mem_top
  rw [iSup_split_single _ w] at hpW
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hpW
  -- The eigenspaces of `D` at distinct integers are independent, so `b = 0`.
  have hind : iSupIndep fun v : ℤ ↦ End.eigenspace D (v : K) :=
    (End.eigenspaces_iSupIndep D).comp Int.cast_injective
  have hD (v : ℤ) : weightSubmodule f g c v ≤ End.eigenspace D (v : K) :=
    fun _ hq ↦ End.mem_eigenspace_iff.2 (mem_weightSubmodule.1 hq).1
  have hbw : b ∈ End.eigenspace D (w : K) := by
    simpa using (End.eigenspace D (w : K)).sub_mem (End.mem_eigenspace_iff.2 hp) (hD w ha)
  have hbne : b ∈ ⨆ (v : ℤ) (_ : v ≠ w), End.eigenspace D (v : K) :=
    iSup₂_mono (fun v _ ↦ hD v) hb
  have hb0 : b = 0 := (Submodule.disjoint_def.1 (hind w)) b hbw hbne
  subst hb0
  rw [add_zero] at hp ⊢
  exact (mem_weightSubmodule.1 ha).2

end SymmetricAlgebra
