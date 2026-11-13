/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
public import TauCeti.Algebra.Lie.HighestWeight.Module
public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.HighestWeight.Weight.Lattice
public import TauCeti.Algebra.Lie.InvariantForm.Basic
public import TauCeti.Algebra.Lie.Sl2.Principal
public import TauCeti.Algebra.Lie.Sl2.WeightMultiplicity
public import TauCeti.Algebra.Lie.Weights.Diagonalizable
import TauCeti.Algebra.Lie.Submodule.Atom
import TauCeti.LinearAlgebra.RootSystem.Weyl.CorootSum

/-!
# Symmetric and alternating invariant forms on irreducible modules

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and `b` a base of its root system,
and let `M` be a finite-dimensional irreducible `L`-module with a highest weight vector of
weight `λ`. A nonzero invariant bilinear form on `M`, when one exists, is either symmetric or
alternating, and which one is decided by the sign

`(-1) ^ ⟨λ, 2ρ^∨⟩`, where `⟨λ, 2ρ^∨⟩ = ∑_{α > 0} ⟨λ, α^∨⟩`

is the sum of the integer pairings of `λ` with the positive coroots: the form is symmetric when
the sign is `1` and alternating when it is `-1`.

Self-duality alone does not decide this: the standard module of `sl₂` is self-dual with an
alternating form, the adjoint module with the symmetric Killing form.

## The proof

The principal `sl₂` triple `(e, 2ρ^∨, f)` of `b` (`TauCeti.exists_isSl2Triple_twoWeylVector_flip`)
turns the highest weight vector `v` into a primitive vector of `2ρ^∨`-eigenvalue
`m = ⟨λ, 2ρ^∨⟩`, since `e` lies in the positive nilradical. Every other weight `μ` of `M` lies
strictly below `λ`, so the integer `⟨μ, 2ρ^∨⟩` is smaller than `m`, the difference being twice a
height (`TauCeti.toLinearMap_twoWeylVector_flip_eq_two_mul_heightLinearMap`): the
`m`-eigenspace of `2ρ^∨` is the line through `v`, and by the symmetry of `sl₂` weight
multiplicities (`TauCeti.finrank_eigenspace_toEnd_neg`) the `-m`-eigenspace is the line through
`w = f ^ m • v`. A nonzero invariant form `Φ` is nondegenerate and pairs the `c`-eigenspace of
`2ρ^∨` only with the `-c`-eigenspace, so `Φ v w ≠ 0`, while invariance moves `f ^ m` across
the form at the cost of the sign `(-1) ^ m`:

`Φ w v = (-1) ^ m * Φ v w`.

Applied to the invariant form `Φᵀ - (-1) ^ m • Φ`, which vanishes at `(v, w)`, this forces
`Φᵀ = (-1) ^ m • Φ`.

## Main results

* `TauCeti.invariantForm_flip_eq_tits_sign_smul`: every invariant form `Φ` on `M` satisfies
  `Φᵀ = (-1) ^ ∑_{α > 0} ⟨λ, α^∨⟩ • Φ`.
* `TauCeti.invariantForm_isSymm_iff_tits_sign`: a nonzero invariant form on `M` is symmetric
  exactly when `(-1) ^ ∑_{α > 0} ⟨λ, α^∨⟩ = 1`.
* `TauCeti.invariantForm_isAlt_iff_tits_sign`: it is alternating exactly when that sign is `-1`.
* `TauCeti.irreducibleQuotient_isSymm_iff_tits_sign` and
  `TauCeti.irreducibleQuotient_isAlt_iff_tits_sign`: the same at the named carrier `L(λ)` of a
  dominant integral weight.

## References

* P. Etingof, *Lie groups and Lie algebras*, lecture notes, Example 32.13 and Proposition 32.14.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VIII, §7.5.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module RootPairing

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {b : (rootSystem H).Base} {lam : Dual K H}

/-! ### The pairing with the sum of the positive coroots -/

/-- A dominant integral weight takes on the sum of the positive coroots the natural number which is
the sum of its integer pairings with the positive coroots. -/
private theorem exists_nat_apply_twoWeylVector_flip (hlam : IsDominantIntegral b lam) :
    ∃ m : ℕ, lam (twoWeylVector (rootSystem H).flip b.flip) = m ∧
      ∑ i ∈ posRootsFinset (rootSystem H) b, coweightPairing lam i = m := by
  set n := ∑ i ∈ posRootsFinset (rootSystem H) b, coweightPairing lam i
  have hn : 0 ≤ n := Finset.sum_nonneg fun i hi ↦
    hlam.coweightPairing_nonneg_of_mem_posRoots ((mem_posRootsFinset _ b i).mp hi)
  refine ⟨n.toNat, ?_, Int.toNat_of_nonneg hn |>.symm⟩
  rw [twoWeylVector_flip_eq_sum_coroot, map_sum, ← Int.cast_natCast, Int.toNat_of_nonneg hn]
  simp only [n, Int.cast_sum, intCast_coweightPairing hlam.isIntegralWeight]

/-! ### The top eigenspace of the sum of the positive coroots -/

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] {v : M}
  [LieModule.IsIrreducible K L M] [FiniteDimensional K M]

/-- **The top eigenspace of `2ρ^∨` is the highest weight line.** Every weight of `M` other than
`λ` lies strictly below `λ`, so it pairs with the sum of the positive coroots to strictly less
than `λ` does; the eigenspace at `⟨λ, 2ρ^∨⟩` is therefore the `λ`-weight space, the line through
the highest weight vector. -/
private theorem eigenspace_twoWeylVector_flip_le (hv : IsHighestWeightVector b lam v) :
    (toEnd K L M ((twoWeylVector (rootSystem H).flip b.flip : H) : L)).eigenspace
      (lam (twoWeylVector (rootSystem H).flip b.flip)) ≤ K ∙ v := by
  set x : H := twoWeylVector (rootSystem H).flip b.flip
  set T := toEnd K L M (x : L)
  have hgen := lieSpan_singleton_eq_top_of_ne_zero (R := K) (L := L) hv.ne_zero
  -- every weight space lies in an eigenspace of `x`
  have hle (χ : H → K) : (genWeightSpace M χ : Submodule K M) ≤ T.eigenspace (χ x) :=
    fun y hy ↦ Module.End.mem_eigenspace_iff.mpr (mem_genWeightSpace_iff_forall_lie_eq_smul.mp hy x)
  -- the weight spaces other than the highest one avoid the eigenvalue `lam x`
  have hlow (χ : H → K) (hχ : χ ≠ ⇑lam) (hχ0 : genWeightSpace M χ ≠ ⊥) : χ x ≠ lam x := by
    let μ : Weight K H M := ⟨χ, hχ0⟩
    have hμ : ((μ : Dual K H) : H → K) = χ := Weight.coe_coe
    have hcone :=
      sub_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top
        hv hgen (chi := μ) (by rw [hμ]; exact hχ0)
    have hne : lam - μ ≠ 0 := fun h ↦ hχ (by rw [← hμ, ← sub_eq_zero.mp h])
    have h := toLinearMap_twoWeylVector_flip_ne_zero_of_mem_posRootCone (rootSystem H) b hcone hne
    rw [rootSystem_toLinearMap_apply, LinearMap.sub_apply, sub_ne_zero] at h
    rw [← hμ]
    exact fun h' ↦ h h'.symm
  -- so `M` is the highest weight line plus the other eigenspaces of `x`
  have htop : ⊤ ≤ (K ∙ v) ⊔ ⨆ (c : K) (_ : c ≠ lam x), T.eigenspace c := by
    rw [← LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top K H M)]
    refine iSup_le fun χ ↦ ?_
    by_cases hχ : χ = ⇑lam
    · subst hχ
      rw [genWeightSpace_eq_span_singleton_of_isHighestWeightVector_of_lieSpan_eq_top hv hgen]
      exact le_sup_left
    by_cases hχ0 : genWeightSpace M χ = ⊥
    · simp [hχ0]
    exact (hle χ).trans (le_sup_of_le_right (le_iSup₂_of_le (χ x) (hlow χ hχ hχ0) le_rfl))
  have hv_mem : v ∈ T.eigenspace (lam x) :=
    Module.End.mem_eigenspace_iff.mpr (hv.lie_eq_smul x)
  intro y hy
  obtain ⟨s, hs, r, hr, rfl⟩ := Submodule.mem_sup.mp (htop (Submodule.mem_top (x := y)))
  -- the component off the highest weight line is an eigenvector for `lam x` as well, hence zero
  have hrE : r ∈ T.eigenspace (lam x) := by
    have hsE : s ∈ T.eigenspace (lam x) :=
      (Submodule.span_singleton_le_iff_mem v _).mpr hv_mem hs
    simpa using sub_mem hy hsE
  have hr0 : r = 0 :=
    (Module.End.eigenspaces_iSupIndep T (lam x)).le_bot ⟨hrE, hr⟩
  simpa [hr0] using hs

/-! ### Pairing the top and bottom eigenspaces -/

omit [CharZero K] [IsKilling K L] [FiniteDimensional K L] [FiniteDimensional K M] in
/-- **A nonzero invariant form pairs an eigenvector with its opposite eigenspace.** Let `x` act
diagonalizably on `M` and let `u ≠ 0` be an eigenvector of eigenvalue `c`. An invariant form pairs
the `c`-eigenspace only with the `-c`-eigenspace, so if that eigenspace lies on the line through
`w` and `Φ` is nonzero, then `Φ u w ≠ 0`. -/
private theorem apply_ne_zero_of_eigenspace_neg_le {Φ : LinearMap.BilinForm K M}
    (hΦ : Φ.lieInvariant L) (hΦ0 : Φ ≠ 0) {x : L} {c : K} {u w : M} (hu0 : u ≠ 0)
    (hu : ⁅x, u⁆ = c • u) (htop : ⨆ μ, (toEnd K L M x).eigenspace μ = ⊤)
    (hw : (toEnd K L M x).eigenspace (-c) ≤ K ∙ w) : Φ u w ≠ 0 := by
  intro huw
  refine hu0 ((hΦ.nondegenerate_of_isIrreducible hΦ0).1 u fun y ↦ ?_)
  have hy : y ∈ ⨆ μ, (toEnd K L M x).eigenspace μ := htop ▸ Submodule.mem_top
  induction hy using Submodule.iSup_induction' with
  | mem μ y hy =>
    by_cases hμ : μ = -c
    · subst hμ
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hw hy)
      simp [huw]
    · exact hΦ.apply_eq_zero_of_mem_eigenspace_of_add_ne_zero
        (Module.End.mem_eigenspace_iff.mpr hu) hy fun h' ↦ hμ (by linear_combination h')
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]

/-- **The principal lowering element pairs the highest weight vector nontrivially.** For the
lowering element `F` of the principal `sl₂` triple, every nonzero invariant form takes a nonzero
value at `(v, F ^ m • v)`, where `m = ⟨λ, 2ρ^∨⟩`. When there is no root, `m = 0` and any `F`
works. -/
private theorem exists_apply_pow_toEnd_ne_zero (hv : IsHighestWeightVector b lam v) {m : ℕ}
    (hm : lam (twoWeylVector (rootSystem H).flip b.flip) = m) :
    ∃ F : L, ∀ Φ : LinearMap.BilinForm K M, Φ.lieInvariant L → Φ ≠ 0 →
      Φ v ((toEnd K L M F ^ m) v) ≠ 0 := by
  set x : H := twoWeylVector (rootSystem H).flip b.flip
  have hvx : ⁅(x : L), v⁆ = (m : K) • v := by rw [hv.lie_eq_smul x, hm]
  have htopE := eigenspace_twoWeylVector_flip_le hv
  rw [hm] at htopE
  rcases isEmpty_or_nonempty H.root with hroot | hroot
  · -- without roots `2ρ^∨ = 0`, so `m = 0` and every vector is an eigenvector
    have hx : x = 0 := by
      simp only [x, twoWeylVector_def, Finset.eq_empty_of_isEmpty, Finset.sum_empty]
    have hm0 : m = 0 := by
      have h : (m : K) = 0 := by rw [← hm, hx, map_zero]
      exact_mod_cast h
    subst hm0
    refine ⟨0, fun Φ hΦ hΦ0 ↦ ?_⟩
    rw [pow_zero, one_apply_eq_self]
    refine apply_ne_zero_of_eigenspace_neg_le hΦ hΦ0 hv.ne_zero hvx ?_ (by simpa using htopE)
    refine eq_top_iff.mpr (le_iSup_of_le 0 fun y _ ↦ ?_)
    simp [hx]
  · obtain ⟨e, F, t, he, -⟩ := exists_isSl2Triple_twoWeylVector_flip b
    have hP : t.HasPrimitiveVectorWith v (m : K) :=
      ⟨hv.ne_zero, hvx, hv.lie_eq_zero_of_mem_positiveNilradical he⟩
    refine ⟨F, fun Φ hΦ hΦ0 ↦ apply_ne_zero_of_eigenspace_neg_le hΦ hΦ0 hv.ne_zero hvx
      (iSup_eigenspace_toEnd_eq_top t) ?_⟩
    -- the bottom eigenspace is a line, as the top one is, and it contains `F ^ m • v`
    set w := (toEnd K L M F ^ m) v
    have hw0 : w ≠ 0 := hP.pow_toEnd_f_ne_zero_of_eq_nat rfl le_rfl
    have hwE : w ∈ (toEnd K L M (x : L)).eigenspace (-(m : K)) := by
      rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply, hP.lie_h_pow_toEnd_f m]
      congr 1
      ring
    have htopEq : (toEnd K L M (x : L)).eigenspace (m : K) = K ∙ v :=
      le_antisymm htopE ((Submodule.span_singleton_le_iff_mem v _).mpr
        (Module.End.mem_eigenspace_iff.mpr hvx))
    have hfin : finrank K (K ∙ w) =
        finrank K ((toEnd K L M (x : L)).eigenspace (-(m : K))) := by
      rw [← finrank_eigenspace_toEnd_neg t, htopEq, finrank_span_singleton hv.ne_zero,
        finrank_span_singleton hw0]
    exact (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem w _).mpr hwE) hfin).ge

/-! ### Symmetric and alternating forms -/

/-- **An invariant form is symmetric up to the sign `(-1) ^ ⟨λ, 2ρ^∨⟩`.** On a finite-dimensional
irreducible module with highest weight `λ`, every invariant bilinear form satisfies
`Φᵀ = (-1) ^ ∑_{α > 0} ⟨λ, α^∨⟩ • Φ`, the sum running over the positive roots of `b` and using the
integer pairings `TauCeti.coweightPairing`. -/
theorem invariantForm_flip_eq_tits_sign_smul (hv : IsHighestWeightVector b lam v)
    {Φ : LinearMap.BilinForm K M} (hΦ : Φ.lieInvariant L) :
    LinearMap.flip Φ =
      (-1 : K) ^ (∑ i ∈ posRootsFinset (rootSystem H) b, coweightPairing lam i) • Φ := by
  obtain ⟨m, hm, hsum⟩ := exists_nat_apply_twoWeylVector_flip hv.isDominantIntegral
  obtain ⟨F, hF⟩ := exists_apply_pow_toEnd_ne_zero hv hm
  rw [hsum, zpow_natCast]
  set w := (toEnd K L M F ^ m) v
  -- `Φᵀ - (-1) ^ m • Φ` is invariant and vanishes at `(v, F ^ m • v)`, so it is zero
  let C : LinearMap.BilinForm K M := LinearMap.flip Φ - (-1 : K) ^ m • Φ
  have hC : C.lieInvariant L := fun x y z ↦ by
    simp only [C, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul,
      hΦ x y z, hΦ x z y]
    ring
  have hCvw : C v w = 0 := by
    simp [C, w, hΦ.apply_pow_toEnd F m v v]
  by_contra hC0
  exact hF C hC (sub_ne_zero.mpr hC0) hCvw

/-- **The symmetry of an invariant form is decided by a sign.** On a finite-dimensional irreducible
module with highest weight `λ`, a nonzero invariant bilinear form is symmetric exactly when
`(-1) ^ ∑_{α > 0} ⟨λ, α^∨⟩ = 1`, the sum running over the positive roots of `b` and using the
integer pairings `TauCeti.coweightPairing`. -/
theorem invariantForm_isSymm_iff_tits_sign (hv : IsHighestWeightVector b lam v)
    {Φ : LinearMap.BilinForm K M} (hΦ : Φ.lieInvariant L) (hΦ0 : Φ ≠ 0) :
    Φ.IsSymm ↔
      (-1 : ℤˣ) ^ (∑ i ∈ posRootsFinset (rootSystem H) b, coweightPairing lam i) = 1 := by
  obtain ⟨m, -, hsum⟩ := exists_nat_apply_twoWeylVector_flip hv.isDominantIntegral
  have hswap (y z : M) : Φ z y = (-1 : K) ^ m * Φ y z := by
    simpa [hsum] using LinearMap.congr_fun₂ (invariantForm_flip_eq_tits_sign_smul hv hΦ) y z
  rw [hsum, zpow_natCast, neg_one_pow_eq_one_iff_even (by decide)]
  refine ⟨fun hs ↦ ?_, fun he ↦ ⟨fun y z ↦ by simpa [he.neg_one_pow] using hswap z y⟩⟩
  -- for odd `m` a symmetric form would equal its negative
  by_contra hodd
  refine hΦ0 (LinearMap.ext₂ fun y z ↦ CharZero.eq_neg_self_iff.mp ?_)
  have h := hswap y z
  rw [(Nat.not_even_iff_odd.mp hodd).neg_one_pow, hs.eq] at h
  simpa using h

/-- **The alternating invariant forms are those of sign `-1`.** On a finite-dimensional irreducible
module with highest weight `λ`, a nonzero invariant bilinear form is alternating exactly when
`(-1) ^ ∑_{α > 0} ⟨λ, α^∨⟩ = -1`. -/
theorem invariantForm_isAlt_iff_tits_sign (hv : IsHighestWeightVector b lam v)
    {Φ : LinearMap.BilinForm K M} (hΦ : Φ.lieInvariant L) (hΦ0 : Φ ≠ 0) :
    Φ.IsAlt ↔
      (-1 : ℤˣ) ^ (∑ i ∈ posRootsFinset (rootSystem H) b, coweightPairing lam i) = -1 := by
  obtain ⟨m, -, hsum⟩ := exists_nat_apply_twoWeylVector_flip hv.isDominantIntegral
  have hswap (y z : M) : Φ z y = (-1 : K) ^ m * Φ y z := by
    simpa [hsum] using LinearMap.congr_fun₂ (invariantForm_flip_eq_tits_sign_smul hv hΦ) y z
  rw [hsum, zpow_natCast, neg_one_pow_eq_neg_one_iff_odd (by decide)]
  refine ⟨fun hs ↦ ?_, fun ho y ↦ CharZero.eq_neg_self_iff.mp (by
    simpa [ho.neg_one_pow] using hswap y y)⟩
  -- for even `m` an alternating form would equal its negative
  by_contra hodd
  refine hΦ0 (LinearMap.ext₂ fun y z ↦ CharZero.eq_neg_self_iff.mp ?_)
  have h := hswap y z
  rw [(Nat.not_odd_iff_even.mp hodd).neg_one_pow, ← LinearMap.IsAlt.neg hs y z] at h
  linear_combination -h

/-! ### At the named carrier `L(λ)` -/

/-- **The symmetry criterion at `L(λ)`.** For dominant integral `λ`, a nonzero invariant bilinear
form on `L(λ)` is symmetric exactly when `(-1) ^ ∑_{α > 0} ⟨λ, α^∨⟩ = 1`. -/
theorem irreducibleQuotient_isSymm_iff_tits_sign (hlam : IsDominantIntegral b lam)
    {Φ : LinearMap.BilinForm K (irreducibleQuotient b lam)} (hΦ : Φ.lieInvariant L)
    (hΦ0 : Φ ≠ 0) :
    Φ.IsSymm ↔
      (-1 : ℤˣ) ^ (∑ i ∈ posRootsFinset (rootSystem H) b, coweightPairing lam i) = 1 := by
  have hgen := isHighestWeightVector_irreducibleQuotientGenerator b lam
  have _j := finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral hgen hlam
  exact invariantForm_isSymm_iff_tits_sign hgen hΦ hΦ0

/-- **The alternating criterion at `L(λ)`.** For dominant integral `λ`, a nonzero invariant
bilinear form on `L(λ)` is alternating exactly when `(-1) ^ ∑_{α > 0} ⟨λ, α^∨⟩ = -1`. -/
theorem irreducibleQuotient_isAlt_iff_tits_sign (hlam : IsDominantIntegral b lam)
    {Φ : LinearMap.BilinForm K (irreducibleQuotient b lam)} (hΦ : Φ.lieInvariant L)
    (hΦ0 : Φ ≠ 0) :
    Φ.IsAlt ↔
      (-1 : ℤˣ) ^ (∑ i ∈ posRootsFinset (rootSystem H) b, coweightPairing lam i) = -1 := by
  have hgen := isHighestWeightVector_irreducibleQuotientGenerator b lam
  have _j := finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral hgen hlam
  exact invariantForm_isAlt_iff_tits_sign hgen hΦ hΦ0

end TauCeti
