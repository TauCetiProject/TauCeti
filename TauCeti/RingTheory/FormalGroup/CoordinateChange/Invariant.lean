/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.HopfAlgebroid
public import TauCeti.RingTheory.FormalGroup.LazardRing.Indecomposable
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.Ideal
import TauCeti.Algebra.Algebra.Rat
import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial
import TauCeti.RingTheory.FormalGroup.Logarithm.InfiniteHeight
import TauCeti.RingTheory.Localization.Int

/-!
# Invariant ideals of the Lazard ring

An ideal `I` of the Lazard ring `L` is **invariant** under the Hopf algebroid
`(L, Γ) = (L, L[b₁, b₂, …])` of strict coordinate changes when its extensions to `Γ` along the
right unit `η_R` and the left unit `η_L = C` agree: `η_R(I) Γ = η_L(I) Γ`. The height ideals
`I_(p, n)` and their union `I_(p, ∞)` are invariant
(`TauCeti.LazardRing.map_rightUnit_heightIdeal`,
`TauCeti.LazardRing.map_rightUnit_iSup_heightIdeal`). Landweber's classification says that, for
each prime `p`, the ideals `I_(p, n)` for `1 ≤ n ≤ ∞` are the homogeneous invariant prime ideals
meeting `ℤ` in `(p)`, and that `0` is the only homogeneous invariant prime ideal meeting `ℤ` in `0`.
This file proves the two extreme cases of that classification, for all ideals, homogeneous and
prime or not:

* an invariant ideal meeting `ℤ` in `0` is `0`
  (`TauCeti.LazardRing.eq_bot_of_map_rightUnit_eq_map_C`);
* for a prime `p`, a proper invariant ideal containing `I_(p, ∞)` is `I_(p, ∞)`
  (`TauCeti.LazardRing.eq_iSup_heightIdeal_of_map_rightUnit_eq_map_C`).

The intermediate heights, which rest on the invariants of `L / I_(p, n)`, are not treated here.

Since `Γ` corepresents strict isomorphisms of commutative formal group laws, an invariant ideal has
the same extension along the classifying maps `f, g : L →+* R` of any two strictly isomorphic
laws over `R` (`TauCeti.LazardRing.map_eq_map_of_isStrict`). When the law classified by `f` is
strictly isomorphic to the additive law, classified by the augmentation `ε : L →+* ℤ`, the
extension of `I` along `f` is the extension of the ideal `ε(I)` of `ℤ`
(`TauCeti.LazardRing.map_eq_map_augmentation_of_isStrict`). Two kinds of law are strictly
isomorphic to the additive law: every commutative law over a `ℚ`-algebra, by its logarithm, and
every commutative law with `[p]_F = 0` for a prime `p`, by its normalised logarithm. The two cases
above apply this to the base changes of the universal law to `L ⊗ ℚ` and to `L / I_(p, ∞)`.

## Main results

* `TauCeti.LazardRing.map_eq_map_of_smul_eq`, `TauCeti.LazardRing.map_eq_map_of_isStrict`: an
  invariant ideal has the same extension along the classifying maps of strictly isomorphic laws.
* `TauCeti.LazardRing.map_eq_map_augmentation_of_isStrict`: comparison with the additive law.
* `TauCeti.LazardRing.eq_bot_of_map_rightUnit_eq_map_C`: an invariant ideal meeting `ℤ` in `0`
  is `0`.
* `TauCeti.LazardRing.eq_iSup_heightIdeal_of_map_rightUnit_eq_map_C`: a proper invariant ideal
  containing `I_(p, ∞)` is `I_(p, ∞)`.

## References

* P. S. Landweber, *Annihilator ideals and primitive elements in complex bordism*, Illinois J.
  Math. 17 (1973), 273–284.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Theorem 1.3.16 and
  Theorem 4.3.2.
-/

public section

namespace TauCeti.LazardRing

open MvPolynomial (C)

variable {R : Type*} [CommRing R]

/-- **Invariant ideals do not see strict coordinate changes.** Let `I` be an ideal of the Lazard
ring whose extensions along the two units of `(L, L[b₁, b₂, …])` agree. If a strict coordinate `φ`
over `R` changes the law classified by `f : L →+* R` into the law classified by `g`, then `I` has
the same extension along `f` and along `g`. -/
theorem map_eq_map_of_smul_eq {I : Ideal LazardRing} (hI : I.map rightUnit = I.map C)
    {f g : LazardRing →+* R} (φ : FormalCoordinate R) (hφ : FormalCoordinate.linearCoeff φ = 1)
    (h : φ • formalGroup.map f = formalGroup.map g) : I.map f = I.map g := by
  -- The strict isomorphism `φ` is classified by a homomorphism `ψ : L[b₁, b₂, …] →+* R`, which
  -- restricts to `f` along the left unit and to `g` along the right unit.
  let ψ := coordinateChangeLift (⟨formalGroup.map f, inferInstance⟩, ⟨φ, MonoidHom.mem_ker.2 hφ⟩)
  have hC : ψ.comp C = f := by
    rw [coordinateChangeLift_comp_C]
    exact hom_ext (map_lift _)
  have hR : ψ.comp rightUnit = g := by
    rw [coordinateChangeLift_comp_rightUnit]
    exact hom_ext ((map_lift _).trans h)
  rw [← hC, ← hR, ← Ideal.map_map, ← Ideal.map_map, hI]

/-- **Invariant ideals have the same extension along strictly isomorphic laws.** If `I` is an ideal
of the Lazard ring whose extensions along the two units of `(L, L[b₁, b₂, …])` agree, and the laws
classified by `f, g : L →+* R` are strictly isomorphic, then `I` has the same extension along `f`
and along `g`. -/
theorem map_eq_map_of_isStrict {I : Ideal LazardRing} (hI : I.map rightUnit = I.map C)
    {f g : LazardRing →+* R} (e : FormalGroupIso (formalGroup.map f) (formalGroup.map g))
    [e.IsStrict] : I.map f = I.map g :=
  map_eq_map_of_smul_eq hI e.toFormalCoordinate e.linearCoeff_toFormalCoordinate
    e.toFormalCoordinate_smul

/-- **Comparison with the additive law.** If `I` is an ideal of the Lazard ring whose extensions
along the two units of `(L, L[b₁, b₂, …])` agree, and the law classified by `f : L →+* R` is
strictly isomorphic to the additive law, then the extension of `I` along `f` is the extension to
`R` of the ideal `ε(I)` of `ℤ`, where `ε` is the augmentation. -/
theorem map_eq_map_augmentation_of_isStrict {I : Ideal LazardRing}
    (hI : I.map rightUnit = I.map C) {f : LazardRing →+* R}
    (e : FormalGroupIso (formalGroup.map f) FormalGroup.𝔾ₐ) [e.IsStrict] :
    I.map f = (I.map augmentation).map (Int.castRingHom R) := by
  rw [Ideal.map_map]
  refine map_eq_map_of_smul_eq hI e.toFormalCoordinate e.linearCoeff_toFormalCoordinate ?_
  rw [e.toFormalCoordinate_smul, ← FormalGroup.map_comp, map_augmentation, FormalGroup.map_𝔾ₐ]

/-- **An invariant ideal of the Lazard ring meeting `ℤ` in `0` is `0`.** If the extensions of an
ideal `I` of `L` along the two units of `(L, L[b₁, b₂, …])` agree and `I` contains no nonzero
integer, then `I = 0`. -/
theorem eq_bot_of_map_rightUnit_eq_map_C {I : Ideal LazardRing} (hI : I.map rightUnit = I.map C)
    (hZ : I.comap (algebraMap ℤ LazardRing) = ⊥) : I = ⊥ := by
  -- `S = L ⊗ ℚ`, the localization of `L` at the nonzero integers. Over `S` the logarithm is a
  -- strict isomorphism from the universal law to the additive law, so `I S` is the extension of
  -- the ideal `ε(I)` of `ℤ`, which must vanish as `I S` is proper; then `I = 0` because `L` is
  -- torsion-free.
  let M := Algebra.algebraMapSubmonoid LazardRing (nonZeroDivisors ℤ)
  let S := Localization M
  have hunit (n : nonZeroDivisors ℤ) : IsUnit (algebraMap ℤ S n) := by
    simpa using TauCeti.IsLocalization.isUnit_intCast_of_mem LazardRing (S := S) n.property
  let _ : Algebra ℚ S := (IsLocalization.lift (S := ℚ) hunit).toRatAlgebra
  have hdisj : Disjoint (M : Set LazardRing) I := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnI
    have h := Ideal.mem_comap.2 hnI
    rw [hZ, Ideal.mem_bot] at h
    exact nonZeroDivisors.coe_ne_zero ⟨n, hn⟩ h
  have hM : M ≤ nonZeroDivisors LazardRing := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by simpa using nonZeroDivisors.coe_ne_zero ⟨n, hn⟩)
  have heq := map_eq_map_augmentation_of_isStrict hI
    (formalGroup.map (algebraMap LazardRing S)).logIso
  -- `ε(I) = 0`: a nonzero integer in `ε(I)` is a unit of `S`, but `I S` is proper.
  have hJ : I.map augmentation = ⊥ := by
    by_contra hJ
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    refine (IsLocalization.map_algebraMap_ne_top_iff_disjoint M S I).2 hdisj ?_
    rw [heq]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hn)
      (by simpa using hunit ⟨n, mem_nonZeroDivisors_of_ne_zero hn0⟩)
  rwa [hJ, Ideal.map_bot, Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective S hM)] at heq

/-- **A proper invariant ideal of the Lazard ring containing `I_(p, ∞)` is `I_(p, ∞)`.** Let `p`
be a prime and `I` a proper ideal of `L` containing the union `I_(p, ∞)` of the height ideals of
the universal law, whose extensions along the two units of `(L, L[b₁, b₂, …])` agree. Then
`I = I_(p, ∞)`. -/
theorem eq_iSup_heightIdeal_of_map_rightUnit_eq_map_C {p : ℕ} (hp : p.Prime)
    {I : Ideal LazardRing} (hI : I.map rightUnit = I.map C)
    (hle : ⨆ n, formalGroup.heightIdeal p n ≤ I) (hne : I ≠ ⊤) :
    I = ⨆ n, formalGroup.heightIdeal p n := by
  -- Over `L / I_(p, ∞)` the `p`-series vanishes, so the normalised logarithm is a strict
  -- isomorphism from the universal law to the additive law, and `I (L / I_(p, ∞))` is the
  -- extension of the ideal `ε(I)` of `ℤ`, which is `(p)` as `I` is proper.
  have : Fact p.Prime := ⟨hp⟩
  set J := ⨆ n, formalGroup.heightIdeal p n
  let f := Ideal.Quotient.mk J
  have hF : (formalGroup.map f).nsmulSeries p = 0 :=
    (FormalGroup.iSup_heightIdeal_le_ker_iff hp.one_lt f).1 (Ideal.mk_ker (I := J)).ge
  obtain ⟨e, he⟩ := (formalGroup.map f).exists_isStrict_formalGroupIso_𝔾ₐ hp hF
  have heq := map_eq_map_augmentation_of_isStrict hI e
  have hpJ : (p : LazardRing) ∈ J := by
    refine Ideal.mem_iSup_of_mem 1 ?_
    rw [formalGroup.heightIdeal_one hp]
    exact Ideal.mem_span_singleton_self _
  -- `ε(I)` contains `p` and is proper, since `I` is, so it is the maximal ideal `(p)` of `ℤ`.
  have hJ : I.map augmentation = Ideal.span {(p : ℤ)} := by
    refine ((Int.ideal_span_isMaximal_of_prime p).eq_of_le ?_ ?_).symm
    · intro htop
      rw [htop, Ideal.map_top] at heq
      have h := Ideal.comap_map_of_surjective' f Ideal.Quotient.mk_surjective I
      rw [heq, Ideal.comap_top, Ideal.mk_ker, sup_eq_left.2 hle] at h
      exact hne h.symm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      simpa using Ideal.mem_map_of_mem augmentation (hle hpJ)
  have hp0 : (p : LazardRing ⧸ J) = 0 := by
    rw [← map_natCast f, Ideal.Quotient.eq_zero_iff_mem]
    exact hpJ
  rw [hJ, Ideal.map_span, Set.image_singleton, map_natCast, hp0, Ideal.span_singleton_eq_bot.2 rfl,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at heq
  exact le_antisymm heq hle

end TauCeti.LazardRing
