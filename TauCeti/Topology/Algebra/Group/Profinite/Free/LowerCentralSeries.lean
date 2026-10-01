/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Abelianization
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Closed
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.ClosedSpan
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Abelianization
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Heisenberg
import TauCeti.Topology.Connected.TotallyDisconnected

/-!
# The closed lower central series of a free pro-`p` group in degrees zero and one

Let `F = freeProP p X` be the free pro-`p` group on a finite type `X`, with generators
`x_i = freeProP.of i`, and let `gr_n(F) = γ_n(F) ⧸ γ_{n+1}(F)` be the graded pieces of its closed
lower central series, the lower `p`-series at `p = 0`. Each `gr_n(F)` is an abelian pro-`p` group,
hence a `ℤ_p`-module, and the bracket `gr_j(F) × gr_k(F) → gr_{j+k+1}(F)` is `ℤ_p`-bilinear. This
file computes the first two pieces:

* `gr_0(F)` is free over `ℤ_p` on the classes `x̄_i` of the generators: the map
  `a ↦ Σ_i [x_i ^ a_i]`, `(X → ℤ_p) → gr_0(F)`, is a bijection;
* for `X` linearly ordered, `gr_1(F)` is free over `ℤ_p` on the brackets `[x̄_i, x̄_j]` for
  `i < j`: the map `c ↦ Σ_{i<j} [⁅x_i, x_j⁆ ^ c_ij]` is a bijection. So `gr_1(F)` is the exterior
  square of `gr_0(F)`, of rank `#X (#X - 1) / 2`;
* in particular `[x̄_i, x̄_j] ≠ 0` for `i ≠ j`.

Here `g ^ a` is the `p`-adic power `TauCeti.IsProP.padicPow`. Both maps are `ℤ_p`-linear, because
the class of `g ^ a` is `a` times the class of `g` (`TauCeti.IsProP.gradedMk_padicPow`), so they
exhibit `ℤ_p`-bases. In contrast to the lower `p`-series,
whose graded pieces are `𝔽_p`-vector spaces (`TauCeti.freeProP.degreeOneBasis`), the `p`-th powers
are not divided out, so the bases are over `ℤ_p` and `gr_1(F)` has no `p`-power part.

Both degrees are proved by detecting homomorphisms supplied by the universal property of `F`. In
degree zero the detector is the exponent-sum map `F → ℤ_p^X`, through the identification of
`gr_0(F)` with the topological abelianization. In degree one, spanning is the one-term spanning
theorem `TauCeti.exists_sum_gradedBracket_eq_of_range` together with bilinearity and alternation,
and the coefficient of `[x̄_i, x̄_j]` is read off by the continuous homomorphism to the Heisenberg
group over `ℤ_p` sending `x_i ↦ (1, 0, 0)`, `x_j ↦ (0, 1, 0)` and the other generators to `1`
(`TauCeti.freeProP.exists_heisenberg_detect`): its closed lower central series stops at `γ_2 = 1`,
and the commutator of the two images is `(0, 0, 1)`.

## Main results

* `TauCeti.lcsGradedPiece_zero_freeProP_bijective`: the classes of the generators form a
  `ℤ_p`-basis of `gr_0(F)`.
* `TauCeti.freeProP.exists_heisenberg_detect`: the detecting homomorphisms to the Heisenberg group.
* `TauCeti.lcsGradedPiece_one_freeProP_bijective`: the brackets `[x̄_i, x̄_j]`, `i < j`, form a
  `ℤ_p`-basis of `gr_1(F)`.
* `TauCeti.lcsBracket_freeProP_ne_zero`: the bracket of two distinct generator classes is nonzero.

## References

* J. Labute, *Algèbres de Lie et pro-p-groupes définis par une seule relation*, Invent. Math. 4
  (1967), 142–158.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV, for discrete free groups.
-/

public section

namespace TauCeti

open Multiplicative
open scoped commutatorElement

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u}

namespace freeProP

/-- **The Heisenberg detecting homomorphisms.** For distinct `i` and `j` there is a continuous
homomorphism from the free pro-`p` group to the Heisenberg group over `ℤ_p` sending `x_i` to
`(1, 0, 0)`, `x_j` to `(0, 1, 0)` and every other generator to `1`. -/
theorem exists_heisenberg_detect {i j : X} (hij : i ≠ j) :
    ∃ f : freeProP p X →* HeisenbergGroup ℤ_[p], Continuous f ∧
      f (of i) = ⟨1, 0, 0⟩ ∧ f (of j) = ⟨0, 1, 0⟩ ∧ ∀ k, k ≠ i → k ≠ j → f (of k) = 1 := by
  classical
  -- The universal property needs a target in the universe of `X`.
  let e : ULift.{u} (HeisenbergGroup ℤ_[p]) ≃ₜ* HeisenbergGroup ℤ_[p] := ContinuousMulEquiv.ulift
  have hP : IsProP p (ULift.{u} (HeisenbergGroup ℤ_[p])) :=
    (HeisenbergGroup.isProP_padicInt p).of_equiv e.symm
  let m : X → HeisenbergGroup ℤ_[p] := fun k ↦
    if k = i then ⟨1, 0, 0⟩ else if k = j then ⟨0, 1, 0⟩ else 1
  let f := (ContinuousMonoidHom.toContinuousMonoidHom e).comp (lift hP (e.symm ∘ m))
  refine ⟨f.toMonoidHom, f.continuous, ?_, ?_, ?_⟩
  · simp [f, lift_of, m]
  · simp [f, lift_of, m, hij.symm]
  · intro k hki hkj
    simp [f, lift_of, m, hki, hkj]

end freeProP

/-- **Nonvanishing of the brackets of generators.** In the degree-one piece of the closed lower
central series of a free pro-`p` group, the bracket of the classes of two distinct generators is
nonzero. -/
theorem lcsBracket_freeProP_ne_zero {i j : X} (hij : i ≠ j) :
    lcsBracket (freeProP p X) 0 0 (gradedMkZero 0 _ (freeProP.of i))
      (gradedMkZero 0 _ (freeProP.of j)) ≠ 0 := by
  obtain ⟨φ, hφc, hφi, hφj, -⟩ := freeProP.exists_heisenberg_detect (p := p) hij
  intro h
  have h' := gradedMap_gradedBracket (p := 0) φ hφc
    (gradedMkZero 0 _ (freeProP.of i)) (gradedMkZero 0 _ (freeProP.of j))
  rw [h, map_zero, gradedMap_gradedMkZero, gradedMap_gradedMkZero, gradedBracket_gradedMkZero,
    eq_comm, gradedMk_eq_zero_iff, Subgroup.coe_mk, hφi, hφj, HeisenbergGroup.commutatorElement_eq,
    ← closedLowerCentralSeries_def, HeisenbergGroup.closedLowerCentralSeries_two_eq_bot,
    Subgroup.mem_bot] at h'
  simpa using congrArg HeisenbergGroup.z h'

variable (p X) [Fintype X]

/-- **The degree-zero basis of a free pro-`p` group.** For the free pro-`p` group `F` on a finite
type `X`, the classes of the generators form a `ℤ_p`-basis of the degree-zero piece of the closed
lower central series: `a ↦ Σ_i [x_i ^ a_i]` is a bijection `(X → ℤ_p) → gr_0(F)`. Through
`TauCeti.lcsGradedPieceZeroEquiv` this is the identification of the topological abelianization of
`F` with `ℤ_p^X`. -/
theorem lcsGradedPiece_zero_freeProP_bijective :
    Function.Bijective fun a : X → ℤ_[p] ↦
      ∑ i, gradedMkZero 0 (freeProP p X)
        ((isProP_freeProP p X).padicPow (freeProP.of i) (a i)) := by
  classical
  -- The coordinates `gr_0(F) ≃ F^{ab} ≃ ℤ_p^X`, given by the exponent sums.
  let Φ : gradedPiece 0 (freeProP p X) 0 →+ (X → ℤ_[p]) :=
    { toFun z := (freeProP.abelianizationEquiv p X (lcsGradedPieceZeroEquiv z).toMul).toAdd
      map_zero' := by simp
      map_add' z w := by simp }
  have hΦ : Function.Injective Φ := fun z w h ↦ lcsGradedPieceZeroEquiv.injective
    (Additive.toMul.injective ((freeProP.abelianizationEquiv p X).injective
      (Multiplicative.toAdd.injective h)))
  have hΦf (a : X → ℤ_[p]) : Φ (∑ i, gradedMkZero 0 (freeProP p X)
      ((isProP_freeProP p X).padicPow (freeProP.of i) (a i))) = a := by
    simp only [map_sum, Φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lcsGradedPieceZeroEquiv_mk,
      toMul_ofMul, freeProP.abelianizationEquiv_mk, freeProP.exponentSum_padicPow_of, toAdd_ofAdd]
    exact Finset.univ_sum_single a
  refine ⟨fun a b h ↦ ?_, fun z ↦ ⟨Φ z, hΦ (hΦf _)⟩⟩
  rw [← hΦf a, ← hΦf b]
  exact congrArg Φ h

section DegreeOne

variable [LinearOrder X]

/-- The class `Σ_{i<j} [⁅x_i, x_j⁆ ^ c_ij]` in `gr_1(F)` of a family of `p`-adic exponents indexed
by the pairs `i < j`: the map of `TauCeti.lcsGradedPiece_one_freeProP_bijective`. -/
private noncomputable def degreeOneSum (c : {ij : X × X // ij.1 < ij.2} → ℤ_[p]) :
    gradedPiece 0 (freeProP p X) 1 :=
  ∑ ij, gradedMk 0 (freeProP p X) 1
    ⟨(isProP_freeProP p X).padicPow ⁅(freeProP.of ij.1.1 : freeProP p X), freeProP.of ij.1.2⁆
        (c ij),
      (isProP_freeProP p X).padicPow_mem (isClosed_pLowerCentralSeries 1)
        (commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 0 _)
          (mem_pLowerCentralSeries_zero 0 _)) (c ij)⟩

/-- The degree-one sum is the `ℤ_p`-linear combination with coefficients `c_ij` of the brackets
`[x̄_i, x̄_j]` of the generator classes. -/
private theorem degreeOneSum_eq_linearCombination (c : {ij : X × X // ij.1 < ij.2} → ℤ_[p]) :
    letI := (isProP_freeProP p X).gradedPieceModule 0 (0 + 0 + 1)
    degreeOneSum p X c = Fintype.linearCombination ℤ_[p] (fun ij : {ij : X × X // ij.1 < ij.2} ↦
      gradedBracket 0 (freeProP p X) 0 0 (gradedMkZero 0 _ (freeProP.of ij.1.1))
        (gradedMkZero 0 _ (freeProP.of ij.1.2))) c := by
  let _ := (isProP_freeProP p X).gradedPieceModule 0 (0 + 0 + 1)
  rw [degreeOneSum, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [(isProP_freeProP p X).gradedMk_padicPow ⟨_, commutator_mem_pLowerCentralSeries
    (mem_pLowerCentralSeries_zero 0 (freeProP.of ij.1.1 : freeProP p X))
    (mem_pLowerCentralSeries_zero 0 (freeProP.of ij.1.2 : freeProP p X))⟩ (c ij),
    gradedBracket_gradedMkZero]

/-- **Reading off the coefficients of a degree-one sum.** If `Σ_{i<j} [⁅x_i, x_j⁆ ^ c_ij] = 0`
then every `c_ab` vanishes: the Heisenberg detecting homomorphism of `(a, b)` kills every term but
the one of `(a, b)`, which it sends to the class of `(0, 0, c_ab)` in `gr_1` of the Heisenberg
group, where `γ_2 = 1`. -/
private theorem eq_zero_of_degreeOneSum_eq_zero {c : {ij : X × X // ij.1 < ij.2} → ℤ_[p]}
    (h : degreeOneSum p X c = 0) : c = 0 := by
  have hF := isProP_freeProP p X
  have hH := HeisenbergGroup.isProP_padicInt p
  funext ⟨⟨a, b⟩, hab⟩
  obtain ⟨φ, hφc, hφa, hφb, hφk⟩ := freeProP.exists_heisenberg_detect (p := p) hab.ne
  have hφ (k l : X) (u : ℤ_[p]) :
      φ (hF.padicPow ⁅(freeProP.of k : freeProP p X), freeProP.of l⁆ u) =
        hH.padicPow ⁅φ (freeProP.of k), φ (freeProP.of l)⁆ u := by
    rw [hF.map_padicPow hH φ hφc, map_commutatorElement]
  have h' := congrArg (gradedMap 0 φ hφc 1) h
  rw [degreeOneSum, map_sum, map_zero, Fintype.sum_eq_single ⟨(a, b), hab⟩] at h'
  · rw [gradedMap_gradedMk, gradedMk_eq_zero_iff, Subgroup.coe_mk, hφ, hφa, hφb,
      HeisenbergGroup.commutatorElement_eq, ← closedLowerCentralSeries_def,
      HeisenbergGroup.closedLowerCentralSeries_two_eq_bot, Subgroup.mem_bot] at h'
    simpa [HeisenbergGroup.padicPow_mk_zero_zero] using congrArg HeisenbergGroup.z h'
  · rintro ⟨⟨k, l⟩, hkl⟩ hne
    rw [gradedMap_gradedMk, gradedMk_eq_zero_iff, Subgroup.coe_mk, hφ]
    -- Unless `(k, l) = (a, b)`, one of `x_k` and `x_l` is sent to `1`.
    have hzero : φ (freeProP.of k) = 1 ∨ φ (freeProP.of l) = 1 := by
      by_cases hka : k = a
      · subst hka
        exact .inr (hφk l hkl.ne' fun hlb ↦ hne (by subst hlb; rfl))
      · by_cases hkb : k = b
        · subst hkb
          exact .inr (hφk l (hab.trans hkl).ne' hkl.ne')
        · exact .inl (hφk k hka hkb)
    rcases hzero with h0 | h0 <;>
      simp only [h0, commutatorElement_one_left, commutatorElement_one_right,
        IsProP.one_padicPow, one_mem]

/-- **Spanning in degree one.** Every class in `gr_1(F)` is a degree-one sum: by the spanning
theorem it is a sum of brackets `[x̄_i, y_i]`, and expanding each `y_i` in the degree-zero basis
makes it a `ℤ_p`-combination of the brackets `[x̄_i, x̄_k]`, which are `0` for `i = k` and
`-[x̄_k, x̄_i]` for `k < i`. -/
private theorem degreeOneSum_surjective : Function.Surjective (degreeOneSum p X) := by
  classical
  have hF := isProP_freeProP p X
  let _ : Module ℤ_[p] (gradedPiece 0 (freeProP p X) 0) := hF.gradedPieceModule 0 0
  let _ : Module ℤ_[p] (gradedPiece 0 (freeProP p X) (0 + 0 + 1)) :=
    hF.gradedPieceModule 0 (0 + 0 + 1)
  let B : X → X → gradedPiece 0 (freeProP p X) (0 + 0 + 1) := fun i j ↦
    gradedBracket 0 (freeProP p X) 0 0 (gradedMkZero 0 _ (freeProP.of i))
      (gradedMkZero 0 _ (freeProP.of j))
  let L := Fintype.linearCombination ℤ_[p] fun ij : {ij : X × X // ij.1 < ij.2} ↦ B ij.1.1 ij.1.2
  have hB (i k : X) : B i k ∈ LinearMap.range L := by
    rcases lt_trichotomy i k with hik | rfl | hik
    · exact ⟨Pi.single ⟨(i, k), hik⟩ 1, by simp [L]⟩
    · rw [show B i i = 0 from gradedBracket_self _]
      exact zero_mem _
    · have hswap : B i k = -B k i := by
        rw [← gradedCast_gradedBracket_swap, gradedCast_rfl]
      rw [hswap]
      exact neg_mem ⟨Pi.single ⟨(k, i), hik⟩ 1, by simp [L]⟩
  have hspan (y : gradedPiece 0 (freeProP p X) 0) :
      ∃ a : X → ℤ_[p], ∑ k, a k • gradedMkZero 0 _ (freeProP.of k) = y := by
    obtain ⟨a, ha⟩ := (lcsGradedPiece_zero_freeProP_bijective p X).2 y
    exact ⟨a, by simpa only [hF.gradedMkZero_padicPow] using ha⟩
  have : CompactSpace (pLowerCentralSeries 0 (freeProP p X) 0) :=
    isCompact_iff_compactSpace.mp (isClosed_pLowerCentralSeries 0).isCompact
  intro z
  simp only [degreeOneSum_eq_linearCombination]
  obtain ⟨y, rfl⟩ := exists_sum_gradedBracket_eq_of_range 0 freeProP.of
    (freeProP.topologicalClosure_closure_range_of_eq_top p X) z
  refine LinearMap.mem_range.mp (Submodule.sum_mem _ fun i _ ↦ ?_)
  obtain ⟨a, ha⟩ := hspan (y i)
  rw [← ha, map_sum]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  rw [hF.gradedBracket_smul_right]
  exact Submodule.smul_mem _ _ (hB i k)

/-- **The degree-one basis of a free pro-`p` group.** For the free pro-`p` group `F` on a finite
linearly ordered type `X`, the brackets `[x̄_i, x̄_j]` of the generator classes for `i < j` form a
`ℤ_p`-basis of the degree-one piece of the closed lower central series: the map
`c ↦ Σ_{i<j} [⁅x_i, x_j⁆ ^ c_ij]` is a bijection `({(i, j) | i < j} → ℤ_p) → gr_1(F)`. It is
`ℤ_p`-linear, because the class of `g ^ u` is `u` times the class of `g`
(`TauCeti.IsProP.gradedMk_padicPow`), so `gr_1(F)` is the exterior square of `gr_0(F)`, with
`x̄_i ∧ x̄_j ↦ [x̄_i, x̄_j]`. -/
theorem lcsGradedPiece_one_freeProP_bijective :
    Function.Bijective fun c : {ij : X × X // ij.1 < ij.2} → ℤ_[p] ↦
      ∑ ij, gradedMk 0 (freeProP p X) 1
        ⟨(isProP_freeProP p X).padicPow
            ⁅(freeProP.of ij.1.1 : freeProP p X), freeProP.of ij.1.2⁆ (c ij),
          (isProP_freeProP p X).padicPow_mem (isClosed_pLowerCentralSeries 1)
            (commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 0 _)
              (mem_pLowerCentralSeries_zero 0 _)) (c ij)⟩ := by
  refine ⟨fun c c' h ↦ ?_, degreeOneSum_surjective p X⟩
  let _ := (isProP_freeProP p X).gradedPieceModule 0 (0 + 0 + 1)
  have h' : degreeOneSum p X (c - c') = 0 := by
    rw [degreeOneSum_eq_linearCombination, map_sub, ← degreeOneSum_eq_linearCombination,
      ← degreeOneSum_eq_linearCombination, degreeOneSum, degreeOneSum]
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp (eq_zero_of_degreeOneSum_eq_zero p X h')

end DegreeOne

end TauCeti
