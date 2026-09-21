/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Root
public import TauCeti.Algebra.Lie.Weights.Chevalley.Twist

/-!
# Constructing Chevalley systems from a Lie-algebra basis

Let a Cartan-inverting automorphism act on a normalised root-vector system by
`ω (x α) = c α • x (-α)`. If `-c α` is a square, rescaling `x α` makes the action equal to the
signed Chevalley involution. This file reduces that square condition to the simple roots via
`RootPairing.Base.induction_add`.

For a `LieAlgebra.Basis` whose simple generators satisfy `ω(eᵢ) = -fᵢ`, write a normalised simple
root vector as `x αᵢ = aᵢ eᵢ`. Its opposite is `aᵢ⁻¹ fᵢ`, so `c αᵢ = -aᵢ²`. Thus the simple-root
square condition holds automatically and a Chevalley system exists over the ground field.

## Main results

* `TauCeti.IsSl2System.isSquare_neg_of_forall_mem_base`: square classes propagate from the simple
  roots to every root.
* `TauCeti.IsSl2System.isSquare_neg_on_lieBasis_base`: a basis exchanged by the automorphism gives
  the required square class at each simple root.
* `TauCeti.IsSl2System.exists_isChevalleySystem_of_lieBasis`: such a basis produces a Chevalley
  system over the ground field.
* `TauCeti.IsChevalleySystem.simple_eq_or_eq_neg_of_lieBasis`: a Chevalley system for the same
  involution agrees with the basis at each simple root up to one simultaneous sign.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

namespace TauCeti

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x)
  (omega : LieEquiv K L L) (homega : ∀ y ∈ H, omega y = -y)

include hx homega

/-- If the negated scalars by which a Cartan-inverting automorphism exchanges root vectors are
squares on the simple roots, then they are squares on every root. -/
theorem isSquare_neg_of_forall_mem_base
    (b : (rootSystem H).Base) (c : Weight K H L → K)
    (hc : ∀ alpha : Weight K H L, alpha.IsNonZero →
      omega (x alpha) = c alpha • x (-alpha))
    (hsimple : ∀ i : b.support, IsSquare (-c (i : Weight K H L)))
    (alpha : Weight K H L) (halpha : alpha.IsNonZero) : IsSquare (-c alpha) := by
  let a : H.root := ⟨alpha, by simpa⟩
  have ha : (a : Weight K H L) = alpha := rfl
  rw [← ha]
  apply b.induction_add (p := fun i : H.root => IsSquare (-c (i : Weight K H L))) a
  · intro i hi
    rw [rootSystem_reflectionPerm_self_eq_neg]
    have hneg : ((-i : H.root) : Weight K H L) = -(i : Weight K H L) := by
      apply Weight.ext
      intro z
      rfl
    have hmul := hx.mul_eq_one_of_map_eq_smul_neg omega homega
      (H.isNonZero_coe_root i) (hc i (H.isNonZero_coe_root i))
      (by simpa using hc (-i) (H.isNonZero_coe_root (-i)))
    have hci : c (-(i : Weight K H L)) = (c (i : Weight K H L))⁻¹ :=
      eq_inv_of_mul_eq_one_right hmul
    rw [hneg, hci]
    simpa using hi.inv
  · intro i hi
    exact hsimple ⟨i, hi⟩
  · intro i j k hijk hi hj
    apply hx.isSquare_neg_of_map_eq_smul_neg omega i j k
      (H.isNonZero_coe_root i) (H.isNonZero_coe_root j) (H.isNonZero_coe_root k)
      (by
        funext z
        simpa only [rootSystem_root_apply, Weight.toLinear_apply, LinearMap.add_apply,
          Pi.add_apply] using LinearMap.congr_fun hijk z)
      (hc i (H.isNonZero_coe_root i)) (hc j (H.isNonZero_coe_root j))
      (hc k (H.isNonZero_coe_root k)) hi (hsimple ⟨j, hj⟩)

omit homega in
/-- At a simple root, a normalised root-vector system differs from the raising and lowering
generators of a Lie-algebra basis by inverse scalars. -/
theorem exists_simple_lieBasis_coefficients
    {ι : Type*} [Fintype ι] (b : LieAlgebra.Basis ι H) (i : b.base.support) :
    ∃ a d : K,
      x i = a • b.e (b.baseSupportEquiv.symm i) ∧
      x (-i) = d • b.f (b.baseSupportEquiv.symm i) ∧ a * d = 1 := by
  let j : ι := b.baseSupportEquiv.symm i
  have hji : b.baseSupportEquiv j = i := b.baseSupportEquiv.apply_symm_apply i
  have hij : ((i : H.root) : H → K) = b.baseSupp j := by
    rw [← b.coe_baseSupportEquiv_apply j, hji]
  have hij_fun : ((i : Weight K H L) : H → K) = (b.baseSupp j : H → K) := hij
  have hi : (i : Weight K H L).IsNonZero := H.isNonZero_coe_root i
  have he_mem : b.e j ∈ rootSpace H (i : Weight K H L) := by
    rw [hij_fun]
    exact lieBasis_e_mem_rootSpace b j
  have hf_mem : b.f j ∈ rootSpace H (-(i : Weight K H L)) := by
    rw [hij_fun]
    exact lieBasis_f_mem_rootSpace b j
  have hx_mem : x i ∈ K ∙ b.e j := by
    rw [← LieAlgebra.IsKilling.toSubmodule_rootSpace_eq_span (i : Weight K H L) hi
      (b.e j) (b.sl2 j).e_ne_zero he_mem]
    exact hx.mem_rootSpace i
  have hx_neg_mem : x (-i) ∈ K ∙ b.f j := by
    rw [← LieAlgebra.IsKilling.toSubmodule_rootSpace_eq_span (-(i : Weight K H L)) hi.neg
      (b.f j) (b.sl2 j).f_ne_zero hf_mem]
    exact hx.mem_rootSpace (-i)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx_mem
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hx_neg_mem
  have ha' : x i = a • b.e j := ha.symm
  have hd' : x (-i) = d • b.f j := hd.symm
  have hcoroot : (coroot (i : Weight K H L) : L) = b.h j := by
    have h := b.coroot_eq_h' j
    rw [hji] at h
    exact congrArg Subtype.val h
  refine ⟨a, d, ha', hd', ?_⟩
  have h := hx.lie_neg (i : Weight K H L) hi
  rw [ha', hd', smul_lie, lie_smul, smul_smul, (b.sl2 j).lie_e_f, hcoroot] at h
  have hh : (coroot (i : Weight K H L) : L) ≠ 0 := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero, coroot_eq_zero_iff] using hi
  exact smul_left_injective K (hcoroot ▸ hh) (by simpa only [one_smul] using h)

omit homega in
/-- A Lie-algebra basis whose simple raising and lowering generators are exchanged with a minus
sign supplies the simple-root square condition for any normalised root-vector system. -/
theorem isSquare_neg_on_lieBasis_base
    {ι : Type*} [Fintype ι] (b : LieAlgebra.Basis ι H) (i : b.base.support)
    (he : omega (b.e (b.baseSupportEquiv.symm i)) =
      -b.f (b.baseSupportEquiv.symm i))
    (c : Weight K H L → K)
    (hc : ∀ alpha : Weight K H L, alpha.IsNonZero →
      omega (x alpha) = c alpha • x (-alpha)) : IsSquare (-c (i : Weight K H L)) := by
  let j : ι := b.baseSupportEquiv.symm i
  have hi : (i : Weight K H L).IsNonZero := H.isNonZero_coe_root i
  obtain ⟨a, d, ha', hd', had⟩ := hx.exists_simple_lieBasis_coefficients b i
  have hd_inv : d = a⁻¹ := eq_inv_of_mul_eq_one_right had
  have ha_ne : a ≠ 0 := left_ne_zero_of_mul_eq_one had
  have hscalar : c (i : Weight K H L) = -(a ^ 2) := by
    have h := hc i hi
    rw [ha', map_smul, he, smul_neg, hd', smul_smul, hd_inv] at h
    have hf_ne : b.f j ≠ 0 := (b.sl2 j).f_ne_zero
    have hs : -a = c (i : Weight K H L) * a⁻¹ :=
      smul_left_injective K hf_ne (by simpa only [neg_smul] using h)
    field_simp [ha_ne] at hs
    exact hs.symm
  rw [hscalar]
  exact ⟨a, by ring⟩

/-- A basis exchanged by a Cartan-inverting automorphism produces a Chevalley system over the
ground field. The simple-root calculation is propagated to all roots through `b.base`. -/
theorem exists_isChevalleySystem_of_lieBasis
    {ι : Type*} [Finite ι] (b : LieAlgebra.Basis ι H)
    (he : ∀ i, omega (b.e i) = -b.f i) :
    ∃ y : Weight K H L → L, IsChevalleySystem omega y := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hnormalizes : H.map omega.toLieHom = H :=
    LieSubalgebra.map_eq_self_of_forall_mem_apply_eq_neg omega homega
  have hscalar : ∀ alpha : Weight K H L, ∃ c : K,
      omega (x alpha) = c • x (-alpha) := by
    intro alpha
    by_cases halpha : alpha.IsNonZero
    · obtain ⟨c, _, hc⟩ := hx.exists_map_eq_smul omega hnormalizes halpha
      refine ⟨c, ?_⟩
      rwa [weightPerm_eq_neg omega homega] at hc
    · refine ⟨0, ?_⟩
      rw [hx.eq_zero_of_isZero alpha (not_not.mp halpha), map_zero, zero_smul]
  choose c hc using hscalar
  have hsquare : ∀ alpha : Weight K H L, alpha.IsNonZero → IsSquare (-c alpha) := by
    intro alpha halpha
    exact hx.isSquare_neg_of_forall_mem_base omega homega b.base c
      (fun beta hbeta => hc beta) (fun i =>
        hx.isSquare_neg_on_lieBasis_base omega b i (he (b.baseSupportEquiv.symm i)) c
          (fun beta hbeta => hc beta)) alpha halpha
  apply hx.exists_isChevalleySystem_of_forall_exists_sq omega homega
  intro alpha halpha
  exact exists_sq_map_eq_smul_neg_of_isSquare (x := x) omega (hc alpha)
    (hsquare alpha halpha)

end IsSl2System

namespace IsChevalleySystem

variable {omega : LieEquiv K L L} {x : Weight K H L → L}
  (hx : IsChevalleySystem omega x)

include hx

/-- At each simple root, a Chevalley system for the basis involution agrees with the basis raising
and lowering generators up to one simultaneous sign. -/
theorem simple_eq_or_eq_neg_of_lieBasis
    {ι : Type*} [Fintype ι] (b : LieAlgebra.Basis ι H) (i : b.base.support)
    (he : omega (b.e (b.baseSupportEquiv.symm i)) =
      -b.f (b.baseSupportEquiv.symm i)) :
    (x i = b.e (b.baseSupportEquiv.symm i) ∧
        x (-i) = b.f (b.baseSupportEquiv.symm i)) ∨
      (x i = -b.e (b.baseSupportEquiv.symm i) ∧
        x (-i) = -b.f (b.baseSupportEquiv.symm i)) := by
  let j : ι := b.baseSupportEquiv.symm i
  obtain ⟨a, d, ha, hd, had⟩ := hx.toIsSl2System.exists_simple_lieBasis_coefficients b i
  have hf_ne : b.f j ≠ 0 := (b.sl2 j).f_ne_zero
  have had_eq : a = d := by
    have h := hx.map_root (i : Weight K H L)
    rw [ha, map_smul, he, hd, smul_neg] at h
    exact smul_left_injective K hf_ne (neg_inj.mp h)
  have ha_sq : a ^ 2 = 1 := by
    simpa [pow_two, had_eq] using had
  rcases sq_eq_one_iff.mp ha_sq with ha_one | ha_neg
  · have hd_one : d = 1 := had_eq.symm.trans ha_one
    exact .inl ⟨by simpa [ha_one] using ha, by simpa [hd_one] using hd⟩
  · have hd_neg : d = -1 := had_eq.symm.trans ha_neg
    exact .inr ⟨by simpa [ha_neg] using ha, by simpa [hd_neg] using hd⟩

end IsChevalleySystem

end TauCeti
