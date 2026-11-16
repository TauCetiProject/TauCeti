/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import TauCeti.AlgebraicGeometry.AffineSpace.Basic
public import TauCeti.RingTheory.MvPolynomial.PolynomialGraph
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Kronecker polynomial graphs in affine space and hypersurface avoidance

For a commutative ring `k` and natural numbers `m` and `B`, the spectrum of
`TauCeti.polynomialGraph k m B : MvPolynomial (Fin m) k →+* Polynomial k` is the Kronecker
polynomial graph morphism
`Spec (.of (Polynomial k)) ⟶ Spec (.of (MvPolynomial (Fin m) k))`
sending `t` to `(t, t ^ B, t ^ (B ^ 2), …, t ^ (B ^ (m - 1)))` over `Spec (.of k)`.

When `0 < m`, `polynomialGraph k m B` is surjective (`TauCeti.polynomialGraph_surjective`), so its
spectrum is a closed immersion of the affine line into affine `m`-space; for `1 ≤ B` it also maps
the origin `Spec.map Polynomial.constantCoeff` of `𝔸¹_k` to the origin
`Spec.map MvPolynomial.constantCoeff` of `𝔸^m_k`. Given any nonzero polynomial
`h : MvPolynomial (Fin m) k` with `0 < m`, choosing `B ≥ 2` larger than every exponent coordinate
in `h.support` yields a closed-immersion Kronecker graph along which `h` pulls back to a nonzero
univariate polynomial (`TauCeti.exists_avoiding_graph`). Over a reduced ring this makes the
preimage of the principal open `D(h)` nonempty, and over an integral domain it makes that preimage
a nonempty dense open of `𝔸¹_k` (`TauCeti.exists_avoiding_graph_dense`), without extending `k`.

## Main results

* `TauCeti.specMap_polynomialGraph_over`, `TauCeti.specMap_polynomialGraph_ulift_specIso_inv`,
  `TauCeti.specMap_polynomialGraph_specIso_inv`: compatibility of the Kronecker graph morphism with
  the `Spec (.of k)` structure maps and with `AlgebraicGeometry.AffineSpace.homOfAlgebra`.
* `TauCeti.specMap_constantCoeff_polynomialGraph`: for `1 ≤ B`, the Kronecker graph maps the origin
  of `𝔸¹_k` to the origin of `𝔸^m_k` (failing at `B = 0` when `2 ≤ m` over a nontrivial ring,
  `TauCeti.specMap_constantCoeff_polynomialGraph_zero_ne`).
* `TauCeti.isClosedImmersion_specMap_polynomialGraph`: for `0 < m`, the Kronecker graph is a closed
  immersion (failing at `m = 0` over a nontrivial ring,
  `TauCeti.not_isClosedImmersion_specMap_polynomialGraph_zero`).
* `TauCeti.exists_avoiding_graph`: for `0 < m` and `h ≠ 0`, there exists `B ≥ 2` exceeding all
  exponent coordinates in `h.support` such that `polynomialGraph k m B h ≠ 0` and
  `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is a closed immersion.
* `TauCeti.nonempty_preimage_basicOpen_polynomialGraph_iff`,
  `TauCeti.dense_preimage_basicOpen_polynomialGraph`, `TauCeti.exists_avoiding_graph_dense`:
  nonemptiness over reduced rings and Zariski density over integral domains of the preimage of
  `PrimeSpectrum.basicOpen h` along the Kronecker graph.
* `TauCeti.preimage_basicOpen_X_one_sub_X_zero_pow_eq_bot`: for `2 ≤ m`, every fixed Kronecker
  graph misses `D(X 1 - X 0 ^ B)`, so `B` must depend on `h`.

## References

* M. Kisin and R. Zhou, *Independence of `ℓ` for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, proofs of Corollary 5.2.7 (pp. 52–53) and Proposition 5.3.5
  (p. 54).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

section CommRing

variable {k : Type u} [CommRing k]

/-- The Kronecker graph `Spec.map (polynomialGraph k m B)` is a morphism of `Spec (.of k)`-schemes.
-/
@[reassoc]
theorem specMap_polynomialGraph_over (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin m) k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, polynomialGraph_comp_algebraMap]

/-- Under `(AffineSpace.SpecIso (ULift (Fin m)) (.of k)).inv`, the Kronecker graph agrees with
`AffineSpace.homOfAlgebra k` for the power tuple `i ↦ X ^ (B ^ i.down)`. -/
theorem specMap_polynomialGraph_ulift_specIso_inv (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.rename (R := k) (ULift.down : ULift.{u} (Fin m) → Fin m)).toRingHom) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (.of k)).inv =
      AffineSpace.homOfAlgebra k
        (fun i : ULift.{u} (Fin m) ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i.down : ℕ))) := by
  rw [AffineSpace.homOfAlgebra_def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine MvPolynomial.ringHom_ext (fun a ↦ by simp) fun i ↦ ?_
  simp

/-- Over `k : Type`, composing `Spec.map (polynomialGraph k m B)` with
`(AffineSpace.SpecIso (Fin m) (.of k)).inv` recovers `AffineSpace.homOfAlgebra k` on
`i ↦ X ^ (B ^ i)`. -/
theorem specMap_polynomialGraph_specIso_inv {k : Type} [CommRing k] (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
      (AffineSpace.SpecIso (Fin m) (.of k)).inv =
      AffineSpace.homOfAlgebra k
        (fun i : Fin m ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))) := by
  rw [AffineSpace.homOfAlgebra_def, aeval_X_pow_toRingHom]

/-- For `1 ≤ B`, the Kronecker graph maps the origin `Spec.map Polynomial.constantCoeff` of `𝔸¹_k`
to the origin `Spec.map MvPolynomial.constantCoeff` of `𝔸^m_k`. -/
@[reassoc]
theorem specMap_constantCoeff_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) :
    Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k))) ≫
      Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, constantCoeff_comp_polynomialGraph hB]

/-- At `B = 0` and `2 ≤ m` over a nontrivial ring `k`, the Kronecker graph sends the origin of
`𝔸¹_k` to `(0, 1, …, 1)` rather than the origin of `𝔸^m_k`. -/
theorem specMap_constantCoeff_polynomialGraph_zero_ne {m : ℕ} (hm : 2 ≤ m) [Nontrivial k] :
    Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k))) ≫
      Spec.map (CommRingCat.ofHom (polynomialGraph k m 0)) ≠
      Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  intro h
  exact constantCoeff_comp_polynomialGraph_zero_ne hm
    (CommRingCat.hom_ext_iff.mp (Spec.map_injective h))

/-- The Kronecker graph `Spec.map (polynomialGraph k m B)` is a closed immersion if and only if
`polynomialGraph k m B` is surjective. -/
theorem isClosedImmersion_specMap_polynomialGraph_iff (m B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) ↔
      Function.Surjective (polynomialGraph k m B) := by
  rw [IsClosedImmersion.hasAffineProperty.SpecMap_iff_of_affineAnd RingHom.surjective_respectsIso]
  rfl

/-- When `0 < m`, the Kronecker graph `Spec.map (polynomialGraph k m B)` is a closed immersion of
`𝔸¹_k` into `𝔸^m_k` for every base `B`. -/
theorem isClosedImmersion_specMap_polynomialGraph {m : ℕ} (hm : 0 < m) (B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) :=
  IsClosedImmersion.spec_of_surjective _ (polynomialGraph_surjective hm B)

/-- Typeclass form of `isClosedImmersion_specMap_polynomialGraph` when `[NeZero m]` is in scope. -/
instance isClosedImmersion_specMap_polynomialGraph_of_neZero {m : ℕ} [NeZero m] (B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) :=
  isClosedImmersion_specMap_polynomialGraph (NeZero.pos m) B

/-- At `m = 0` over a nontrivial ring `k`, `Spec.map (polynomialGraph k 0 B)` is the structural
projection `𝔸¹_k ⟶ Spec (.of k)`, which is not a closed immersion. -/
theorem not_isClosedImmersion_specMap_polynomialGraph_zero [Nontrivial k] (B : ℕ) :
    ¬ IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k 0 B))) := by
  rw [isClosedImmersion_specMap_polynomialGraph_iff]
  exact not_surjective_polynomialGraph_zero B

/-- **A Kronecker graph avoiding a hypersurface.** For `m > 0` and a nonzero polynomial `h` in `m`
variables over a commutative ring `k`, there is a base `B ≥ 2` exceeding every exponent coordinate
in the support of `h` such that `polynomialGraph k m B h ≠ 0` and the graph
`Spec (.of (Polynomial k)) ⟶ Spec (.of (MvPolynomial (Fin m) k))` is a closed immersion. -/
theorem exists_avoiding_graph {k : Type*} [CommRing k] {m : ℕ} (hm : 0 < m)
    {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph k m B h ≠ 0 ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) := by
  obtain ⟨B, hB, hsupp, hne⟩ := exists_polynomialGraph_ne_zero hh
  exact ⟨B, hB, hsupp, hne, isClosedImmersion_specMap_polynomialGraph hm B⟩

/-- For `2 ≤ m`, every fixed Kronecker graph `Spec.map (polynomialGraph k m B)` maps all of `𝔸¹_k`
into the hypersurface `V(X 1 - X 0 ^ B)`, so the preimage of `D(X 1 - X 0 ^ B)` is empty. -/
theorem preimage_basicOpen_X_one_sub_X_zero_pow_eq_bot {m : ℕ} (hm : 2 ≤ m) (B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen
        (MvPolynomial.X ⟨1, hm⟩ - MvPolynomial.X ⟨0, by omega⟩ ^ B : MvPolynomial (Fin m) k) =
      ⊥ := by
  rw [SpecMap_preimage_basicOpen]
  exact (PrimeSpectrum.basicOpen_eq_bot_iff _).mpr (by simp)

end CommRing

/-! ### Principal opens over reduced rings and integral domains -/

section ReducedAndDomain

variable {k : Type u} [CommRing k]

/-- Over a reduced commutative ring `k`, the preimage of the principal open
`PrimeSpectrum.basicOpen h` along `Spec.map (polynomialGraph k m B)` is nonempty if and only if
`polynomialGraph k m B h ≠ 0`. -/
theorem nonempty_preimage_basicOpen_polynomialGraph_iff [IsReduced k] (m B : ℕ)
    (h : MvPolynomial (Fin m) k) :
    (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h :
      Set (Spec (.of (Polynomial k)))).Nonempty ↔
      polynomialGraph k m B h ≠ 0 := by
  rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty, ne_eq, SpecMap_preimage_basicOpen]
  refine (PrimeSpectrum.basicOpen_eq_bot_iff (polynomialGraph k m B h)).not.trans ?_
  refine not_iff_not.mpr ⟨fun hnil ↦ ?_, fun h0 ↦ by simp [h0]⟩
  ext i
  simpa using isNilpotent_iff_eq_zero.mp (Polynomial.isNilpotent_iff.mp hnil i)

/-- Over an integral domain `k`, whenever `polynomialGraph k m B h ≠ 0`, the preimage of
`PrimeSpectrum.basicOpen h` along `Spec.map (polynomialGraph k m B)` is Zariski dense in
`Spec (.of (Polynomial k))`. -/
theorem dense_preimage_basicOpen_polynomialGraph [IsDomain k] {m B : ℕ}
    {h : MvPolynomial (Fin m) k} (hne : polynomialGraph k m B h ≠ 0) :
    Dense (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h :
      Set (Spec (.of (Polynomial k)))) :=
  (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h).isOpen.dense
    ((nonempty_preimage_basicOpen_polynomialGraph_iff m B h).mpr hne)

/-- Over an integral domain `k` (in particular over any field), for `0 < m` and a nonzero
polynomial `h : MvPolynomial (Fin m) k`, there exists a base `B ≥ 2` exceeding every exponent
coordinate in `h.support` such that the Kronecker graph is a closed immersion preserving the origin
and pulling back `PrimeSpectrum.basicOpen h` to a nonempty dense open of `𝔸¹_k`. -/
theorem exists_avoiding_graph_dense [IsDomain k] {m : ℕ} (hm : 0 < m)
    {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) ∧
      Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k))) ≫
        Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := k))) ∧
      (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h :
        Set (Spec (.of (Polynomial k)))).Nonempty ∧
      Dense (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h :
        Set (Spec (.of (Polynomial k)))) := by
  obtain ⟨B, hB, hsupp, hne, hci⟩ := exists_avoiding_graph hm hh
  exact ⟨B, hB, hsupp, hci, specMap_constantCoeff_polynomialGraph (by omega),
    (nonempty_preimage_basicOpen_polynomialGraph_iff m B h).mpr hne,
    dense_preimage_basicOpen_polynomialGraph hne⟩

end ReducedAndDomain

/-! ### Examples -/

section Examples

/-- Over `ZMod 4`, the hypothesis `[IsReduced k]` in
`nonempty_preimage_basicOpen_polynomialGraph_iff` cannot be dropped: `h = 2 X₀` is nonzero and
`polynomialGraph (ZMod 4) 1 2 h = 2 X ≠ 0`, yet `2 X` is nilpotent so the preimage of `D(h)` is
empty. -/
example :
    let h : MvPolynomial (Fin 1) (ZMod 4) := MvPolynomial.C 2 * MvPolynomial.X 0
    polynomialGraph (ZMod 4) 1 2 h ≠ 0 ∧
      Spec.map (CommRingCat.ofHom (polynomialGraph (ZMod 4) 1 2)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen h = ⊥ := by
  dsimp only
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · have hc : (2 : ZMod 4) = 0 := by simpa using congrArg (fun p ↦ p.coeff 1) h0
    exact absurd hc (by decide)
  · rw [SpecMap_preimage_basicOpen]
    refine (PrimeSpectrum.basicOpen_eq_bot_iff _).mpr ⟨2, ?_⟩
    have hp : (CommRingCat.ofHom (polynomialGraph (ZMod 4) 1 2))
        (MvPolynomial.C 2 * MvPolynomial.X 0) = Polynomial.C 2 * Polynomial.X := by simp
    have h2 : (2 : ZMod 4) ^ 2 = 0 := by decide
    rw [hp, mul_pow, ← Polynomial.C_pow, h2]
    simp

end Examples

end

end TauCeti
