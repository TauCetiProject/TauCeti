/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Shuffle.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# The orthonormal-mask Hilbert carrier of a Hecke shuffle module

The shuffle representation acts on `PiLp 2 (fun _ : ShuffleMask k l => U)`, with its
ordinary sum inner product, not a norm transported from an induced module. If the rest
module's generators are symmetric and the parameter is real, the shuffle generators are
symmetric too. If the rest generators act continuously, every algebra element acts
continuously, without requiring completeness or a real parameter.

A unitary intertwiner of rest modules extends coordinatewise by identity on masks. This is
the native `LinearIsometryEquiv.piLpCongrRight`; it is a linear isometry equivalence that
intertwines the shuffle actions.
The statements include empty selected and empty rest blocks.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52, for induction from parabolic subalgebras.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Chapter 3.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ} {k l : ℕ}
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
variable (k) (ρ : TypeAHeckeAlgebra 𝕜 q l →ₐ[𝕜] Module.End 𝕜 U)

/-- The shuffle representation on the ordinary orthonormal-mask carrier. Its inner product
is `∑ S, ⟪f S, g S⟫`, as given by `PiLp.inner_apply`. -/
noncomputable def shuffleHilbertRep :
    TypeAHeckeAlgebra 𝕜 q (k + l) →ₐ[𝕜]
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l => U) :=
  ((WithLp.linearEquiv 2 𝕜 (ShuffleMask k l → U)).symm.conjAlgEquiv 𝕜).toAlgHom.comp
    (shuffleRep k ρ)

/-- Passing to the Hilbert carrier does not change any mask coordinate of the action. -/
@[simp]
theorem shuffleHilbertRep_apply (x : TypeAHeckeAlgebra 𝕜 q (k + l))
    (f : PiLp 2 fun _ : ShuffleMask k l => U) (S : ShuffleMask k l) :
    shuffleHilbertRep k ρ x f S = shuffleRep k ρ x (WithLp.ofLp f) S := (rfl)

private theorem sum_inner_shuffleRep_T (hq : star (q : 𝕜) = q)
    (hρ : ∀ i, (ρ (T q i)).IsSymmetric) (i : Fin (k + l - 1))
    (f g : ShuffleMask k l → U) :
    ∑ S, ⟪shuffleRep k ρ (T q i) f S, g S⟫_𝕜 =
      ∑ S, ⟪f S, shuffleRep k ρ (T q i) g S⟫_𝕜 := by
  classical
  let a := BraidGroup.strand i
  let b := BraidGroup.strandSucc i
  let e : Equiv.Perm (ShuffleMask k l) :=
    Function.Involutive.toPerm (fun S => S.swap a b) (fun S => S.swap_swap a b)
  let h (S : ShuffleMask k l) : 𝕜 :=
    if (a ∈ S.1 ∧ b ∉ S.1) ∨ (a ∉ S.1 ∧ b ∈ S.1) then ⟪f S, g (e S)⟫_𝕜 else 0
  have he (S : ShuffleMask k l) : e S = S.swap a b := (rfl)
  have hp (S : ShuffleMask k l) :
      ⟪shuffleRep k ρ (T q i) f S, g S⟫_𝕜 =
        ⟪f S, shuffleRep k ρ (T q i) g S⟫_𝕜 + (h S - h (e S)) := by
    by_cases ha : a ∈ S.1 <;> by_cases hb : b ∈ S.1
    · simp [h, he, ha, hb, a, b, inner_smul_left, inner_smul_right, starRingEnd_apply, hq]
    · simp [h, he, ha, hb, a, b, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, map_sub, starRingEnd_apply, hq]
    · simp [h, he, ha, hb, a, b, inner_neg_left, inner_neg_right]
      ring
    · simpa [h, he, ha, hb, a, b] using
        hρ ⟨S.restIndex a, ShuffleMask.restIndex_lt_sub_one (by simp [a, b, Fin.lt_def]) ha hb⟩
          (f S) (g S)
  simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp e h, sub_self, add_zero]

/-- Real parameters and symmetric rest generators give symmetric shuffle generators in the
specified sum inner product. In particular this applies to `q = √Q` for `Q > 0`. -/
theorem isSymmetric_shuffleHilbertRep_T (hq : star (q : 𝕜) = q)
    (hρ : ∀ i, (ρ (T q i)).IsSymmetric) (i : Fin (k + l - 1)) :
    (shuffleHilbertRep k ρ (T q i)).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, shuffleHilbertRep_apply]
  exact sum_inner_shuffleRep_T k ρ hq hρ i _ _

/-- If the rest generators act continuously, every shuffle operator is bounded. No
completeness, finite-dimensionality, symmetry or real-parameter hypothesis is required. -/
theorem continuous_shuffleHilbertRep (hρ : ∀ i, Continuous (ρ (T q i)))
    (x : TypeAHeckeAlgebra 𝕜 q (k + l)) :
    Continuous (shuffleHilbertRep k ρ x) := by
  have hx : x ∈ Algebra.adjoin 𝕜 (Set.range (T (n := k + l) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    classical
    -- Expose the conjugation defining shuffleHilbertRep as toLp ∘ shuffleRep ∘ ofLp
    -- so continuous_toLp applies; the coordinate lemma alone does not rewrite this map.
    change Continuous (fun f => WithLp.toLp 2 (shuffleRep k ρ (T q i) (WithLp.ofLp f)))
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro S
    by_cases ha : BraidGroup.strand i ∈ S.1 <;>
      by_cases hb : BraidGroup.strandSucc i ∈ S.1
    · simp only [shuffleRep_T_apply_of_mem_of_mem ρ ha hb]
      exact (PiLp.continuous_apply 2 _ S).const_smul _
    · simp only [shuffleRep_T_apply_of_mem_of_notMem ρ ha hb]
      exact ((PiLp.continuous_apply 2 _ S).const_smul _).sub
        (PiLp.continuous_apply 2 _ _)
    · simp only [shuffleRep_T_apply_of_notMem_of_mem ρ ha hb]
      exact (PiLp.continuous_apply 2 _ _).neg
    · simp only [shuffleRep_T_apply_of_notMem_of_notMem ρ ha hb]
      exact (hρ _).comp (PiLp.continuous_apply 2 _ S)
  | algebraMap r =>
    rw [AlgHom.commutes, Module.algebraMap_end_eq_smul_id]
    exact continuous_const.smul continuous_id
  | add x y _ _ hx hy => simpa using hx.add hy
  | mul x y _ _ hx hy => simpa using hx.comp hy

/-- The whole shuffle action respects the real-parameter involution: the action of `star x`
is adjoint to that of `x` in the ordinary mask inner product. -/
theorem inner_shuffleHilbertRep_star [Fact (IsSelfAdjoint (q : 𝕜))]
    (hρ : ∀ i, (ρ (T q i)).IsSymmetric) (x : TypeAHeckeAlgebra 𝕜 q (k + l))
    (f g : PiLp 2 fun _ : ShuffleMask k l => U) :
    ⟪shuffleHilbertRep k ρ x f, g⟫_𝕜 = ⟪f, shuffleHilbertRep k ρ (star x) g⟫_𝕜 := by
  have hx : x ∈ Algebra.adjoin 𝕜 (Set.range (T (n := k + l) q)) := by
    rw [adjoin_range_T]
    trivial
  -- Multiplication applies the induction hypotheses to transformed vectors.
  induction hx using Algebra.adjoin_induction generalizing f g with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa only [star_T] using
      isSymmetric_shuffleHilbertRep_T k ρ (IsSelfAdjoint.star_eq (Fact.out)) hρ i f g
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
    simp only [map_smul, map_one, LinearMap.smul_apply, one_apply_eq_self,
      inner_smul_left, inner_smul_right, starRingEnd_apply]
  | add x y _ _ hx hy => simp [inner_add_left, inner_add_right, hx, hy]
  | mul x y _ _ hx hy =>
    simpa only [map_mul, mul_apply_eq_comp, star_mul] using (hx _ g).trans (hy f _)

end TauCeti.TypeAHeckeAlgebra

namespace LinearIsometryEquiv

open TauCeti TypeAHeckeAlgebra

variable {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ} {k l : ℕ}
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {ρ : TauCeti.TypeAHeckeAlgebra 𝕜 q l →ₐ[𝕜] Module.End 𝕜 U}
variable {ρ' : TauCeti.TypeAHeckeAlgebra 𝕜 q l →ₐ[𝕜] Module.End 𝕜 V}

/-- A unitary rest-module intertwiner, extended by identity on masks, is a unitary
intertwiner for the full shuffle actions. -/
theorem piLpCongrRight_shuffleHilbertRep (e : U ≃ₗᵢ[𝕜] V)
    (he : ∀ i, e.toLinearMap ∘ₗ ρ (T q i) = ρ' (T q i) ∘ₗ e.toLinearMap)
    (x : TypeAHeckeAlgebra 𝕜 q (k + l)) (f : PiLp 2 fun _ : ShuffleMask k l => U) :
    LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ShuffleMask k l => e)
        (shuffleHilbertRep k ρ x f) =
      shuffleHilbertRep k ρ' x
        (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ShuffleMask k l => e) f) := by
  apply PiLp.ext
  intro S
  simp only [piLpCongrRight_apply, PiLp.toLp_apply, shuffleHilbertRep_apply]
  have hcomp (g : ShuffleMask k l → U) :
      e.toLinearMap.compLeft (ShuffleMask k l) g = fun S => e (g S) := by
    funext S
    simp only [LinearMap.compLeft_apply, Function.comp_apply, LinearEquiv.coe_coe,
      coe_toLinearEquiv]
  simpa only [LinearMap.comp_apply, hcomp] using
    congrFun (LinearMap.congr_fun (compLeft_comp_shuffleRep e.toLinearMap he x)
      (WithLp.ofLp f)) S

end LinearIsometryEquiv
