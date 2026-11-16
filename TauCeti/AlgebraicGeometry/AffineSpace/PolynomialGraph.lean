/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineSpace.Basic
public import TauCeti.RingTheory.MvPolynomial.PolynomialGraph

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Kronecker polynomial graphs in affine space and hypersurface avoidance

For a commutative ring `k` and natural numbers `m, B`, the spectrum
`Spec.map (CommRingCat.ofHom (TauCeti.polynomialGraph k m B))` of the base-`B` Kronecker
substitution is the polynomial-graph morphism
`Spec k[T] ⟶ Spec k[X_0, …, X_{m-1}]`, `T ↦ (T, T ^ B, T ^ (B ^ 2), …, T ^ (B ^ (m - 1)))`.

* Under the canonical isomorphism `AlgebraicGeometry.AffineSpace.SpecIso (Fin m) (.of k)` (for
  `k : Type`, matching the universe of `Fin m : Type`), this morphism corresponds to
  `AlgebraicGeometry.AffineSpace.homOfAlgebra k (fun i : Fin m ↦ X ^ (B ^ i))`
  (`TauCeti.homOfAlgebra_X_pow_specIso_hom`).
* It lies over `Spec (.of k)` (`TauCeti.specMap_polynomialGraph_comp_C`), sends the origin of
  `𝔸¹_k` to the origin of `𝔸^m_k` when `B ≥ 1` (`TauCeti.origin_specMap_polynomialGraph`), is an
  isomorphism for `m = 1` (`TauCeti.isIso_specMap_polynomialGraph_one`), and is a closed immersion
  whenever `m > 0` (`TauCeti.isClosedImmersion_specMap_polynomialGraph`), and in fact if and only
  if `m > 0` when `k` is nontrivial (`TauCeti.isClosedImmersion_specMap_polynomialGraph_iff`).
* Given any nonzero polynomial `h ∈ k[X_0, …, X_{m-1}]` in `m > 0` variables, choosing a base
  `B ≥ 2` strictly above every exponent in `h.support` yields a closed-immersion polynomial graph
  through the origin on which `h` pulls back to a nonzero univariate polynomial
  (`TauCeti.exists_avoiding_graph`).
* When `k` is reduced (`[IsReduced k]`), the preimage of `PrimeSpectrum.basicOpen h` along the
  graph is nonempty whenever `polynomialGraph k m B h ≠ 0`
  (`TauCeti.nonempty_preimage_basicOpen_polynomialGraph`); when `k` is an integral domain
  (`[IsDomain k]`), `Spec (.of (Polynomial k))` is irreducible, so this preimage is also Zariski
  dense (`TauCeti.dense_preimage_basicOpen_polynomialGraph`,
  `TauCeti.exists_avoiding_graph_basicOpen`).

## Main results

* `TauCeti.isClosedImmersion_specMap_polynomialGraph`,
  `TauCeti.isClosedImmersion_specMap_polynomialGraph_iff`: for `m > 0`, the Kronecker graph
  `Spec k[T] ⟶ Spec k[X_0, …, X_{m-1}]` is a closed immersion (and conversely when `Nontrivial k`).
* `TauCeti.origin_specMap_polynomialGraph`: for `B ≥ 1`, the Kronecker graph sends the origin of
  `𝔸¹_k` to the origin of `𝔸^m_k`.
* `TauCeti.exists_avoiding_graph`: for `m > 0` and `h ≠ 0`, there exists `B ≥ 2` exceeding all
  exponents in `h.support` such that `polynomialGraph k m B h ≠ 0` and
  `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is a closed immersion.
* `TauCeti.nonempty_preimage_basicOpen_polynomialGraph`,
  `TauCeti.dense_preimage_basicOpen_polynomialGraph`, `TauCeti.exists_avoiding_graph_basicOpen`:
  nonemptiness (over a reduced ring) and Zariski density (over an integral domain) of the
  pulled-back principal open `PrimeSpectrum.basicOpen h`.

## References

* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, *Annals of Mathematics* 202 (2025), no. 3 (arXiv:2103.09945v2, §§5.2–5.3, pp. 52–54).
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  Exercise 3.5.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory AlgebraicGeometry MvPolynomial

/-- Under `AffineSpace.SpecIso (Fin m) (.of k)` (`k : Type`, matching the universe of
`Fin m : Type`), `AffineSpace.homOfAlgebra` for the coordinate tuple `i ↦ X ^ (B ^ i)` agrees with
`Spec.map (CommRingCat.ofHom (polynomialGraph k m B))`. -/
@[reassoc]
theorem homOfAlgebra_X_pow_specIso_hom (k : Type) [CommRing k] (m B : ℕ) :
    AffineSpace.homOfAlgebra k (fun i : Fin m ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))) ≫
        (AffineSpace.SpecIso (Fin m) (.of k)).hom =
      Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) := by
  rw [AffineSpace.homOfAlgebra_specIso_hom, polynomialGraph_eq_aeval]
  rfl

/-- `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` commutes with the structure morphisms to
`Spec (.of k)`. -/
@[reassoc (attr := simp)]
theorem specMap_polynomialGraph_comp_C (k : Type*) [CommRing k] (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, polynomialGraph_comp_C]

/-- For `B ≥ 1`, `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` maps the origin
`Spec.map (CommRingCat.ofHom Polynomial.constantCoeff)` of `𝔸¹_k` to the origin
`Spec.map (CommRingCat.ofHom MvPolynomial.constantCoeff)` of `𝔸^m_k`. -/
@[reassoc]
theorem origin_specMap_polynomialGraph {k : Type*} [CommRing k] {m B : ℕ} (hB : 1 ≤ B) :
    Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k))) ≫
        Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, constantCoeff_comp_polynomialGraph hB]

/-- On one variable, `CommRingCat.ofHom (polynomialGraph k 1 B)` is an isomorphism for every `B`. -/
instance isIso_ofHom_polynomialGraph_one (k : Type*) [CommRing k] (B : ℕ) :
    IsIso (CommRingCat.ofHom (polynomialGraph k 1 B)) := by
  rw [polynomialGraph_one_var]
  exact (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.toCommRingCatIso.isIso_hom

/-- On one variable, `Spec.map (CommRingCat.ofHom (polynomialGraph k 1 B))` is an isomorphism for
every `B` (including `B = 0`). -/
instance isIso_specMap_polynomialGraph_one (k : Type*) [CommRing k] (B : ℕ) :
    IsIso (Spec.map (CommRingCat.ofHom (polynomialGraph k 1 B))) :=
  inferInstance

/-- For `m > 0`, the Kronecker graph `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is a
closed immersion for every base `B` (including `B = 0`). -/
theorem isClosedImmersion_specMap_polynomialGraph {k : Type*} [CommRing k] {m : ℕ} (hm : 0 < m)
    (B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) :=
  IsClosedImmersion.spec_of_surjective _ (polynomialGraph_surjective hm B)

/-- On zero variables over a nontrivial commutative ring,
`Spec.map (CommRingCat.ofHom (polynomialGraph k 0 B))` is not a closed immersion. -/
theorem not_isClosedImmersion_specMap_polynomialGraph_zero (k : Type*) [CommRing k] [Nontrivial k]
    (B : ℕ) :
    ¬ IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k 0 B))) := by
  rw [IsClosedImmersion.hasAffineProperty.SpecMap_iff_of_affineAnd RingHom.surjective_respectsIso,
    CommRingCat.hom_ofHom]
  exact not_surjective_polynomialGraph_zero k B

/-- Over a nontrivial commutative ring, `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is a
closed immersion if and only if `0 < m`. -/
@[simp]
theorem isClosedImmersion_specMap_polynomialGraph_iff {k : Type*} [CommRing k] [Nontrivial k]
    {m B : ℕ} :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) ↔ 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [not_isClosedImmersion_specMap_polynomialGraph_zero]
  · exact ⟨fun _ ↦ hm, fun _ ↦ isClosedImmersion_specMap_polynomialGraph hm B⟩

/-- **A Kronecker graph avoiding a hypersurface.** For `m > 0` and a nonzero polynomial `h` in `m`
variables over a commutative ring `k`, there exists a base `B ≥ 2` exceeding every exponent in
`h.support` such that `polynomialGraph k m B h ≠ 0` and
`Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is a closed immersion. -/
theorem exists_avoiding_graph {k : Type*} [CommRing k] {m : ℕ} (hm : 0 < m)
    {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph k m B h ≠ 0 ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) := by
  obtain ⟨B, hB, hsupp, hne⟩ := exists_polynomialGraph_ne_zero hh
  exact ⟨B, hB, hsupp, hne, isClosedImmersion_specMap_polynomialGraph hm B⟩

/-! ### Principal opens, nonemptiness, and Zariski density -/

/-- Over a reduced commutative ring `k`, if `polynomialGraph k m B h ≠ 0`, then the preimage of
`PrimeSpectrum.basicOpen h` along `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is
nonempty. -/
theorem nonempty_preimage_basicOpen_polynomialGraph {k : Type*} [CommRing k] [IsReduced k]
    {m B : ℕ} {h : MvPolynomial (Fin m) k} (hne : polynomialGraph k m B h ≠ 0) :
    ((Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen h : (Spec (.of (Polynomial k))).Opens) :
        Set (Spec (.of (Polynomial k)))).Nonempty := by
  have : IsReduced (Polynomial k) :=
    ⟨fun p hp ↦ by ext n; exact (Polynomial.isNilpotent_iff.mp hp n).eq_zero⟩
  rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty, SpecMap_preimage_basicOpen,
    ← basicOpen_eq_of_affine, CommRingCat.ofHom_apply, ne_eq, basicOpen_eq_bot_iff]
  intro h0
  exact hne (by simpa using congrArg (Scheme.ΓSpecIso (.of (Polynomial k))).hom h0)

/-- Over an integral domain `k`, if `polynomialGraph k m B h ≠ 0`, then the preimage of
`PrimeSpectrum.basicOpen h` along `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is Zariski
dense in `Spec (.of (Polynomial k))`. -/
theorem dense_preimage_basicOpen_polynomialGraph {k : Type*} [CommRing k] [IsDomain k]
    {m B : ℕ} {h : MvPolynomial (Fin m) k} (hne : polynomialGraph k m B h ≠ 0) :
    Dense ((Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen h : (Spec (.of (Polynomial k))).Opens) :
        Set (Spec (.of (Polynomial k)))) :=
  (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
    PrimeSpectrum.basicOpen h).isOpen.dense
    (nonempty_preimage_basicOpen_polynomialGraph hne)

/-- Over an integral domain `k`, for `m > 0` and any nonzero `h : MvPolynomial (Fin m) k`, there
exists `B ≥ 2` exceeding every exponent in `h.support` such that the Kronecker graph
`Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is a closed immersion sending the origin of
`𝔸¹_k` to the origin of `𝔸^m_k`, and the preimage of `PrimeSpectrum.basicOpen h` is nonempty and
Zariski dense in `Spec (.of (Polynomial k))`. -/
theorem exists_avoiding_graph_basicOpen {k : Type*} [CommRing k] [IsDomain k] {m : ℕ} (hm : 0 < m)
    {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) ∧
      Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k))) ≫
          Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := k))) ∧
      ((Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen h : (Spec (.of (Polynomial k))).Opens) :
          Set (Spec (.of (Polynomial k)))).Nonempty ∧
      Dense ((Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen h : (Spec (.of (Polynomial k))).Opens) :
          Set (Spec (.of (Polynomial k)))) := by
  obtain ⟨B, hB, hsupp, hne, hclosed⟩ := exists_avoiding_graph hm hh
  exact ⟨B, hB, hsupp, hclosed, origin_specMap_polynomialGraph (by omega),
    nonempty_preimage_basicOpen_polynomialGraph hne,
    dense_preimage_basicOpen_polynomialGraph hne⟩

/-! ### Geometric negative controls -/

/-- No single base `B` avoids every hypersurface in `m ≥ 2` variables: the polynomial
`X 1 - X 0 ^ B` defines a principal open whose preimage along
`Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is empty. -/
theorem preimage_basicOpen_X_sub_X_pow {k : Type*} [CommRing k] {m : ℕ} (hm : 2 ≤ m) (B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen
        (MvPolynomial.X ⟨1, hm⟩ - MvPolynomial.X ⟨0, by omega⟩ ^ B) = ⊥ := by
  rw [SpecMap_preimage_basicOpen, ← basicOpen_eq_of_affine, CommRingCat.ofHom_apply,
    polynomialGraph_X_sub_X_pow, map_zero, Scheme.basicOpen_zero]

/-- Over a nontrivial commutative ring and in `m ≥ 2` variables, for every base `B` there exists a
nonzero polynomial `h` whose principal open pulls back to `⊥` along
`Spec.map (CommRingCat.ofHom (polynomialGraph k m B))`. -/
theorem exists_ne_zero_preimage_basicOpen_polynomialGraph_eq_bot (k : Type*) [CommRing k]
    [Nontrivial k] {m : ℕ} (hm : 2 ≤ m) (B : ℕ) :
    ∃ h : MvPolynomial (Fin m) k, h ≠ 0 ∧
      Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h = ⊥ := by
  obtain ⟨h, hne, h0⟩ := exists_ne_zero_polynomialGraph_eq_zero k hm B
  refine ⟨h, hne, ?_⟩
  rw [SpecMap_preimage_basicOpen, ← basicOpen_eq_of_affine, CommRingCat.ofHom_apply, h0, map_zero,
    Scheme.basicOpen_zero]

/-- `[IsReduced k]` cannot be dropped from `nonempty_preimage_basicOpen_polynomialGraph`: over
`ZMod 4`, the constant polynomial `2 : MvPolynomial (Fin 1) (ZMod 4)` is nonzero and has nonzero
image under `polynomialGraph (ZMod 4) 1 B`, yet the preimage of `PrimeSpectrum.basicOpen 2` is
empty because `2` is nilpotent in `Polynomial (ZMod 4)`. -/
example (B : ℕ) :
    let h : MvPolynomial (Fin 1) (ZMod 4) := 2
    h ≠ 0 ∧ polynomialGraph (ZMod 4) 1 B h ≠ 0 ∧
      Spec.map (CommRingCat.ofHom (polynomialGraph (ZMod 4) 1 B)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen h = ⊥ := by
  have h2 : (2 : ZMod 4) ≠ 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    exact h2 (by simpa [map_ofNat] using congrArg MvPolynomial.constantCoeff h0)
  · intro h0
    have hc := congrArg Polynomial.constantCoeff h0
    exact h2 (by simpa [← map_ofNat MvPolynomial.C 2] using hc)
  · rw [SpecMap_preimage_basicOpen, ← basicOpen_eq_of_affine, CommRingCat.ofHom_apply,
      ← (Spec (.of (Polynomial (ZMod 4)))).basicOpen_pow _ (n := 2) (by decide),
      ← map_pow, ← map_pow, ← map_ofNat MvPolynomial.C 2, ← map_pow]
    have h4 : (2 : ZMod 4) ^ 2 = 0 := by decide
    simp [h4]

end TauCeti

end
