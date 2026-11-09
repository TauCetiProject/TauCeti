/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.PowerSeries.Ideal
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Pullback
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Spf
public import TauCeti.Examples.AlgebraicGeometry.Morphisms.Thickening
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.RingTheory.AdicCompletion.Topology
public import TauCeti.RingTheory.PowerSeries.AdicComplete
public import TauCeti.RingTheory.RegularLocalRing.PowerSeries
public import TauCeti.RingTheory.Spectrum.Prime.Finite
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Examples of adic thickening systems and formal spectra

This file illustrates the definitions and sharpness of `AdicThickeningSystem`, `AdicRing`, and
`Spf` on standard algebro-geometric and arithmetic examples:

* `adic_tower_cubic_rejected`: the tower `Spec k ⟶ Spec (k[t] ⧸ (t³)) = Spec (k[t] ⧸ (t³)) = ⋯`
  has thickenings for all transitions, yet fails the adic power equation `(ι 1).ker =
  (levelMap X ι 2).ker ^ 2`, since `(ι 1).ker = ⊥` while `(t)² = (t²) ≠ 0` in `k[t] ⧸ (t³)`.
* `Spf.padicInt_points`: every level of `Spf ℤ_[p]` has a unique point.
* `Spf.isoOfIdealEqBot` and `Spf.ofScheme`: for an adic ring with zero ideal of definition,
  `Spf A` is isomorphic to the constant system `Spec A`, and any commutative ring viewed as a
  constant system is `Spf` with the zero ideal.
* `Spf.not_spec_powerSeries`: every level of `Spf k⟦t⟧` has `1` point whereas `Spec k⟦t⟧` has `2`
  points (generic and closed), so `Spf k⟦t⟧` is not isomorphic to the constant system `Spec k⟦t⟧`.
* `Spf.homEquivPadic`: every ring endomorphism of `ℤ_[p]` is the identity, so `Spf ℤ_[p]` has a
  unique endomorphism.
* `padicLineLevelIso`: the `n`-th level of the fibre product of `𝔸¹_{ℤ_[p]}` with `Spf ℤ_[p]` over
  `Spec ℤ_[p]` is isomorphic to `𝔸¹_{ℤ/p^{n+1}ℤ}`.
* `not_adic_projection`: the morphism `Spf k⟦s⟧⟦t⟧ ⟶ Spf k⟦s⟧` induced by the coefficient
  inclusion `s ↦ s` is not adic, since `(s)` does not generate an ideal of definition of
  `k⟦s⟧⟦t⟧`.
* `not_levelPreserving_powerSeries`: the identity of `k⟦t⟧` is continuous from the `(t)`-adic to
  the `(t²)`-adic topology because `(t)² = (t²)`, yet `(t) ⊈ (t²)`, so it does not correspond to a
  level-preserving morphism `Spf (k⟦t⟧, (t²)) ⟶ Spf (k⟦t⟧, (t))`.
* `locallyNoetherian_padic`: `Spf ℤ_[p]` and `Spf k⟦t⟧` are locally Noetherian, as concrete
  instances of `Spf.isLocallyNoetherian`.

## References

* [Stacks Project, Definition 87.9.9](https://stacks.math.columbia.edu/tag/0AIF).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace TauCeti.AlgebraicGeometry

/-! ### 1. A tower of thickenings that is not adic -/

/-- A tower of thickenings need not satisfy the adic power equation: taking `X 0 = Spec (k[t]/(t))`
and `X (n + 1) = Spec (k[t]/(t³))` with the quotient transition followed by identities gives
thickenings at every step, but `(ι 1).ker = ⊥` while `(levelMap X ι 2).ker ^ 2 ≠ ⊥`. -/
theorem adic_tower_cubic_rejected (k : Type u) [Field k] :
    let A := k[X] ⧸ Ideal.span {(Polynomial.X : k[X]) ^ 3}
    ∃ (X : ℕ → Scheme.{u}) (ι : ∀ n, X n ⟶ X (n + 1)),
      Nonempty (X 0 ≅ Spec (.of k)) ∧
      (∀ n, Nonempty (X (n + 1) ≅ Spec (.of A))) ∧
      (∀ n, IsThickening (ι n)) ∧ (∀ n, IsIso (ι (n + 1))) ∧
      (ι 1).ker = ⊥ ∧ (levelMap X ι 2).ker ^ 2 ≠ ⊥ ∧
      (ι 1).ker ≠ (levelMap X ι 2).ker ^ 2 := by
  intro A
  let X : ℕ → Scheme.{u}
    | 0 => Spec (.of (k[X] ⧸ Ideal.span {(Polynomial.X : k[X])}))
    | _ + 1 => Spec (.of A)
  have hle : Ideal.span {(Polynomial.X : k[X]) ^ 3} ≤ Ideal.span {(Polynomial.X : k[X])} :=
    Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self (Polynomial.X : k[X]) three_ne_zero)
  let ι : ∀ n, X n ⟶ X (n + 1)
    | 0 => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle))
    | _ + 1 => 𝟙 _
  refine ⟨X, ι, ?_, fun _ ↦ ⟨Iso.refl _⟩, ?_, fun _ ↦ inferInstance, ?_, ?_, ?_⟩
  · -- `k[X] ⧸ (X) ≃+* k` by evaluation at `0`.
    let e : (k[X] ⧸ Ideal.span {(Polynomial.X : k[X])}) ≃+* k :=
      (Ideal.quotEquivOfEq (by simp :
        Ideal.span {(Polynomial.X : k[X])} = Ideal.span {Polynomial.X - Polynomial.C 0})).trans
        (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toRingEquiv
    exact ⟨Scheme.Spec.mapIso e.symm.toCommRingCatIso.op⟩
  · rintro (_ | n)
    · exact isThickening_cube k
    · exact inferInstanceAs (IsThickening (𝟙 (Spec (.of A))))
  · exact Scheme.Hom.ker_eq_bot_of_isIso (ι 1)
  · have hlev : levelMap X ι 2 = ι 0 := by simp [X, ι]
    rw [hlev, pow_two]
    intro hsq
    have : IsClosedImmersion (ι 0) := (isThickening_cube k).toIsClosedImmersion
    exact not_isFirstOrderThickening_cube k ⟨hsq⟩
  · intro heq
    rw [Scheme.Hom.ker_eq_bot_of_isIso (ι 1)] at heq
    have hlev : levelMap X ι 2 = ι 0 := by simp [X, ι]
    rw [hlev, pow_two] at heq
    have : IsClosedImmersion (ι 0) := (isThickening_cube k).toIsClosedImmersion
    exact not_isFirstOrderThickening_cube k ⟨heq.symm⟩

/-! ### 2. Points of formal spectra of `ℤ_[p]` and `k⟦t⟧` -/

/-- The ring of `p`-adic integers `ℤ_[p]` as an `AdicRing` with its maximal ideal `(p)`. -/
noncomputable abbrev AdicRing.padicInt (p : ℕ) [Fact p.Prime] : AdicRing.{0} where
  carrier := ℤ_[p]
  ideal := IsLocalRing.maximalIdeal ℤ_[p]
  fg := IsNoetherian.noetherian _

/-- Every level of `Spf ℤ_[p]` has a unique underlying point. -/
theorem Spf.padicInt_points (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Nonempty (Unique ((Spf (AdicRing.padicInt p)).X n)) :=
  ⟨AdicThickeningSystem.uniqueSpfMaximalIdeal ℤ_[p] n⟩

/-- When the ideal of definition of an adic ring `A` is zero, `Spf A` is isomorphic to the constant
system associated to `Spec A`. -/
noncomputable example (A : AdicRing.{u}) (h : A.ideal = ⊥) :
    Spf A ≅ AdicThickeningSystem.ofScheme.obj (Spec (.of A.carrier)) :=
  Spf.isoOfIdealEqBot A h

/-- A commutative ring viewed as a constant adic thickening system is isomorphic to `Spf` with the
zero ideal of definition. -/
noncomputable example (R : Type u) [CommRing R] :
    AdicThickeningSystem.ofScheme.obj (Spec (.of R)) ≅ Spf (AdicRing.ofBot R) :=
  (Spf.ofScheme R).symm

/-- Formal power series `k⟦X⟧` over a field `k` as an `AdicRing` with maximal ideal `(X)`. -/
noncomputable abbrev AdicRing.powerSeries (k : Type u) [Field k] : AdicRing.{u} where
  carrier := PowerSeries k
  ideal := IsLocalRing.maximalIdeal (PowerSeries k)
  fg := IsNoetherian.noetherian _
  complete := by
    have : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
      rw [(IsLocalRing.maximalIdeal k).eq_bot_of_prime]
      infer_instance
    infer_instance

/-- Every level of `Spf k⟦t⟧` has `1` point while `Spec k⟦t⟧` has `2` points, so `Spf k⟦t⟧` is not
isomorphic to the constant system `Spec k⟦t⟧`. -/
theorem Spf.not_spec_powerSeries (k : Type u) [Field k] :
    (∀ n, Nat.card ((Spf (AdicRing.powerSeries k)).X n) = 1) ∧
    Nat.card (Spec (.of (PowerSeries k))) = 2 ∧
    IsEmpty (Spf (AdicRing.powerSeries k) ≅
      AdicThickeningSystem.ofScheme.obj (Spec (.of (PowerSeries k)))) := by
  have hcard1 : ∀ n, Nat.card ((Spf (AdicRing.powerSeries k)).X n) = 1 := fun n ↦ by
    have : Unique ((Spf (AdicRing.powerSeries k)).X n) :=
      AdicThickeningSystem.uniqueSpfMaximalIdeal (PowerSeries k) n
    exact Nat.card_unique
  have hcard2 : Nat.card (Spec (.of (PowerSeries k))) = 2 :=
    PrimeSpectrum.natCard_of_krullDimLE_one PowerSeries.not_isField
  refine ⟨hcard1, hcard2, ⟨fun e ↦ ?_⟩⟩
  have h := Nat.card_congr
    (IsUniversalHomeomorphism.isHomeomorph (e.hom.app 0)).homeomorph.toEquiv
  rw [AdicThickeningSystem.ofScheme_obj_X, hcard1 0, hcard2] at h
  omega

/-! ### 3. Endomorphisms of `Spf ℤ_[p]` -/

/-- Because `ℤ_[p]` has only the identity ring endomorphism (`PadicInt.ringHom_eq_id`), `Spf ℤ_[p]`
has a unique endomorphism in `AdicThickeningSystem`. -/
@[instance_reducible]
noncomputable def Spf.homEquivPadic (p : ℕ) [Fact p.Prime] :
    Unique (Spf (AdicRing.padicInt p) ⟶ Spf (AdicRing.padicInt p)) where
  default := 𝟙 _
  uniq f := by
    apply (Spf.homEquiv (AdicRing.padicInt p) (AdicRing.padicInt p)).injective
    ext1
    exact Subsingleton.elim _ _

/-! ### 4. The `p`-adic formal affine line -/

/-- The `p`-adic formal affine line, obtained as the pullback of `𝔸¹_{ℤ_[p]} ⟶ Spec ℤ_[p]` along
`Spf ℤ_[p] ⟶ Spec ℤ_[p]`. -/
noncomputable def padicLine (p : ℕ) [Fact p.Prime] : AdicThickeningSystem.{0} :=
  AdicThickeningSystem.pullback (Spf.toSpec (AdicRing.padicInt p))
    (AdicThickeningSystem.ofScheme.map (𝔸(Unit; Spec (.of ℤ_[p])) ↘ Spec (.of ℤ_[p])))

/-- The `n`-th level of the `p`-adic formal affine line is isomorphic to `𝔸¹` over
`ℤ / p ^ (n + 1) ℤ`. -/
noncomputable def padicLineLevelIso (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicLine p).X n ≅ 𝔸(Unit; Spec (.of (ZMod (p ^ (n + 1))))) := by
  have hpow : IsLocalRing.maximalIdeal ℤ_[p] ^ (n + 1) = Ideal.span {(p : ℤ_[p]) ^ (n + 1)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  let ringIso : (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p] ^ (n + 1)) ≃+* ZMod (p ^ (n + 1)) :=
    (Ideal.quotEquivOfEq hpow).trans (PadicInt.quotientSpanPowEquivZMod (n + 1))
  let baseIso : (Spf (AdicRing.padicInt p)).X n ≅ Spec (.of (ZMod (p ^ (n + 1)))) :=
    Scheme.Spec.mapIso ringIso.symm.toCommRingCatIso.op
  let lineIso : 𝔸(Unit; (Spf (AdicRing.padicInt p)).X n) ≅
      𝔸(Unit; Spec (.of (ZMod (p ^ (n + 1))))) :=
    { hom := AffineSpace.map Unit baseIso.hom
      inv := AffineSpace.map Unit baseIso.inv
      hom_inv_id := by rw [← AffineSpace.map_comp, baseIso.hom_inv_id, AffineSpace.map_id]
      inv_hom_id := by rw [← AffineSpace.map_comp, baseIso.inv_hom_id, AffineSpace.map_id] }
  exact (AffineSpace.isPullback_map (n := Unit)
    ((Spf.toSpec (AdicRing.padicInt p)).app n)).flip.isoPullback.symm ≪≫ lineIso

/-! ### 5. A morphism of formal spectra that is not adic -/

/-- Formal power series in two variables `k⟦s⟧⟦t⟧` as an `AdicRing` with its maximal ideal
`(s, t)`. -/
noncomputable abbrev AdicRing.powerSeries₂ (k : Type u) [Field k] : AdicRing.{u} where
  carrier := PowerSeries (PowerSeries k)
  ideal := IsLocalRing.maximalIdeal (PowerSeries (PowerSeries k))
  fg := IsNoetherian.noetherian _
  complete := by
    have : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) :=
      (AdicRing.powerSeries k).complete
    infer_instance

/-- The coefficient inclusion `k⟦s⟧ →+* k⟦s⟧⟦t⟧` maps `(s)` into `(s, t)`, yet the induced morphism
`Spf k⟦s⟧⟦t⟧ ⟶ Spf k⟦s⟧` is not adic because `(s)` does not generate `(s, t)` modulo `(s, t)²`. -/
theorem not_adic_projection (k : Type u) [Field k] :
    have hC : (AdicRing.powerSeries k).ideal ≤
        (AdicRing.powerSeries₂ k).ideal.comap PowerSeries.C := by
      intro f hf
      dsimp only [AdicRing.powerSeries, AdicRing.powerSeries₂] at hf ⊢
      rw [Ideal.mem_comap, TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff,
        Ideal.mem_comap, PowerSeries.constantCoeff_C]
      exact hf
    ¬ AdicThickeningSystem.IsAdicHom
      (Spf.map (A := AdicRing.powerSeries k) (B := AdicRing.powerSeries₂ k) PowerSeries.C hC) := by
  intro hC hadic
  have h0 := (Spf.isAdicHom_map_iff (A := AdicRing.powerSeries k) (B := AdicRing.powerSeries₂ k)
    (φ := PowerSeries.C) hC).mp hadic 0
  dsimp only [AdicRing.powerSeries, AdicRing.powerSeries₂, Nat.zero_add] at h0
  rw [pow_one, pow_one] at h0
  let m₁ := IsLocalRing.maximalIdeal (PowerSeries k)
  let m₂ := IsLocalRing.maximalIdeal (PowerSeries (PowerSeries k))
  -- Every series in `m₁.map C` has linear coefficient in `m₁` (in fact all coefficients in `m₁`).
  have hmap : ∀ y ∈ m₁.map (PowerSeries.C : PowerSeries k →+* PowerSeries (PowerSeries k)),
      PowerSeries.coeff 1 y ∈ m₁ := by
    let π := PowerSeries.map (Ideal.Quotient.mk m₁)
    have hle : m₁.map PowerSeries.C ≤ RingHom.ker π :=
      Ideal.map_le_iff_le_comap.mpr fun g hg ↦ by
        simp [π, PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hg]
    intro y hy
    have hy0 : PowerSeries.coeff 1 (π y) = 0 := by rw [RingHom.mem_ker.mp (hle hy), map_zero]
    rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem] at hy0
    exact hy0
  -- Every series in `m₂ ^ 2` also has linear coefficient in `m₁ ^ (2 - 1) = m₁`.
  have hsq : ∀ z ∈ m₂ ^ 2, PowerSeries.coeff 1 z ∈ m₁ := by
    intro z hz
    have hz' : z ∈ (m₁.comap PowerSeries.constantCoeff) ^ 2 := by
      dsimp only [m₁, m₂] at hz ⊢
      rwa [← TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff]
    simpa using (PowerSeries.mem_comap_constantCoeff_pow_iff m₁).mp hz' 1
  -- Yet the outer indeterminate `X` lies in `m₂` and has linear coefficient `1 ∉ m₁`.
  have hX : (PowerSeries.X : PowerSeries (PowerSeries k)) ∈ m₂ := by
    dsimp only [m₂]
    rw [TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff, Ideal.mem_comap,
      PowerSeries.constantCoeff_X]
    exact m₁.zero_mem
  dsimp only [m₂] at hX
  rw [← h0, Submodule.mem_sup] at hX
  rcases hX with ⟨y, hy, z, hz, hyz⟩
  have h1 : (1 : PowerSeries k) ∈ m₁ := by
    have hcoeff : PowerSeries.coeff 1 (y + z) ∈ m₁ := by
      rw [map_add]
      exact m₁.add_mem (hmap y hy) (hsq z hz)
    simpa [hyz] using hcoeff
  exact (IsLocalRing.maximalIdeal.isMaximal (PowerSeries k)).ne_top
    (Ideal.eq_top_iff_one m₁ |>.mpr h1)

/-! ### 6. A continuous ring map that is not level-preserving -/

/-- `k⟦t⟧` equipped with the chosen ideal of definition `(t)`. -/
noncomputable abbrev powerSeriesSpanX (k : Type u) [Field k] : AdicRing.{u} where
  carrier := PowerSeries k
  ideal := Ideal.span {(PowerSeries.X : PowerSeries k)}
  fg := Submodule.fg_span_singleton _
  complete := by
    rw [← PowerSeries.maximalIdeal_eq_span_X]
    exact (AdicRing.powerSeries k).complete

/-- `k⟦t⟧` equipped with the chosen ideal of definition `(t²)`, which defines the same topology as
`(t)` since `(t²) = (t)²`. -/
noncomputable abbrev powerSeriesSpanXSq (k : Type u) [Field k] : AdicRing.{u} where
  carrier := PowerSeries k
  ideal := Ideal.span {(PowerSeries.X : PowerSeries k) ^ 2}
  fg := Submodule.fg_span_singleton _
  complete := by
    let I₁ : Ideal (PowerSeries k) := (powerSeriesSpanX k).ideal
    let _ : TopologicalSpace (PowerSeries k) := I₁.adicTopology
    have : IsTopologicalRing (PowerSeries k) := I₁.nonarchimedean.toIsTopologicalRing
    have h₂ : IsAdic (Ideal.span {(PowerSeries.X : PowerSeries k) ^ 2}) := by
      rw [← Ideal.span_singleton_pow]
      exact is_ideal_adic_pow (J := I₁) rfl Nat.zero_lt_two
    exact (IsAdic.isAdicComplete_iff_of_isAdic (I := I₁) rfl h₂).mp
      (powerSeriesSpanX k).complete

/-- The identity of `k⟦t⟧` is continuous from the `(t)`-adic topology to the `(t²)`-adic topology,
yet `(t) ⊈ (t²)`, so there is no morphism `Spf (k⟦t⟧, (t²)) ⟶ Spf (k⟦t⟧, (t))` in
`AdicThickeningSystem` inducing the identity on global sections. -/
theorem not_levelPreserving_powerSeries (k : Type u) [Field k] :
    @Continuous (PowerSeries k) (PowerSeries k)
      (powerSeriesSpanX k).ideal.adicTopology
      (powerSeriesSpanXSq k).ideal.adicTopology (RingHom.id (PowerSeries k)) ∧
    ¬ (powerSeriesSpanX k).ideal ≤ (powerSeriesSpanXSq k).ideal.comap (RingHom.id _) ∧
    ¬ ∃ f : Spf (powerSeriesSpanXSq k) ⟶ Spf (powerSeriesSpanX k),
        (Spf.homEquiv (powerSeriesSpanX k) (powerSeriesSpanXSq k) f).1 = RingHom.id _ := by
  have htop : (powerSeriesSpanX k).ideal.adicTopology =
      (powerSeriesSpanXSq k).ideal.adicTopology := by
    let I₁ := (powerSeriesSpanX k).ideal
    let _ : TopologicalSpace (PowerSeries k) := I₁.adicTopology
    have : IsTopologicalRing (PowerSeries k) := I₁.nonarchimedean.toIsTopologicalRing
    have h₂ : IsAdic (Ideal.span {(PowerSeries.X : PowerSeries k) ^ 2}) := by
      rw [← Ideal.span_singleton_pow]
      exact is_ideal_adic_pow (J := I₁) rfl Nat.zero_lt_two
    exact h₂
  have hnotle : ¬ (powerSeriesSpanX k).ideal ≤
      (powerSeriesSpanXSq k).ideal.comap (RingHom.id (PowerSeries k)) := by
    intro hle
    have hmem : (PowerSeries.X : PowerSeries k) ∈
        Ideal.span {(PowerSeries.X : PowerSeries k) ^ 2} :=
      hle (Ideal.subset_span (Set.mem_singleton _))
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hmem
    have h1 := hmem 1 (by omega)
    simp at h1
  refine ⟨?_, hnotle, ?_⟩
  · let _ : TopologicalSpace (PowerSeries k) := (powerSeriesSpanX k).ideal.adicTopology
    rw [← htop]
    exact continuous_id
  · rintro ⟨f, hf⟩
    have hle := (Spf.homEquiv (powerSeriesSpanX k) (powerSeriesSpanXSq k) f).2
    rw [hf] at hle
    exact hnotle hle

/-! ### 7. Locally Noetherian formal spectra -/

/-- `Spf ℤ_[p]` and `Spf k⟦t⟧` are locally Noetherian, as concrete instances of
`Spf.isLocallyNoetherian`. -/
theorem locallyNoetherian_padic (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] :
    (Spf (AdicRing.padicInt p)).IsLocallyNoetherian ∧
    (Spf (AdicRing.powerSeries k)).IsLocallyNoetherian :=
  ⟨Spf.isLocallyNoetherian (AdicRing.padicInt p),
   Spf.isLocallyNoetherian (AdicRing.powerSeries k)⟩

end TauCeti.AlgebraicGeometry
