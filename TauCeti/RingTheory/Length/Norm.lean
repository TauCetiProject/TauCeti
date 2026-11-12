/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import TauCeti.RingTheory.Length.Determinant
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.RingHom.Surjective
import TauCeti.RingTheory.OrderOfVanishing

/-!
# The order of a norm

Let `A` be a Noetherian domain of Krull dimension at most one with fraction field `K`, and let `B`
be a domain that is a finite `A`-algebra, with fraction field `L`. For a nonzero `b : B`, this
file computes the order of the norm `N_{L/K}(b)` in two steps (Fulton, *Intersection Theory*,
Appendix A.3):

* `TauCeti.ordFrac_norm_eq_coe_of_length_eq`: the order of `N_{L/K}(b)` is the `A`-length of
  `B ⧸ bB`. The norm need not lie in `A`, since `A` need not be integrally closed, so its order is
  Mathlib's `Ring.ordFrac A` on `K`. This is Fulton's determinant lemma (Appendix A.2)
  (`LinearMap.ordFrac_det_eq_coe_of_length_eq`) for multiplication by `b` on the lattice `B ⊆ L`,
  which spans `L` over `K` because `B` is integral over `A`
  (`TauCeti.span_range_algebraMap_eq_top`).
* `TauCeti.length_quotient_span_singleton_eq_finsum_ord`: for `A` local, that length is
  `Σ_m ord_{B_m}(b) [κ(B_m) : κ(A)]` over the maximal ideals `m` of `B`. The Artinian ring
  `B ⧸ bB` is the product of its localizations
  (`TauCeti.length_quotient_span_singleton_eq_finsum`),
  the localization of `B ⧸ bB` at `m` is `B_m ⧸ b B_m`
  (`TauCeti.length_localization_quotient_span_singleton`), and Mathlib's
  `IsLocalRing.length_restrictScalars` converts lengths over `B_m` into lengths over `A`.

Together they give `ord_A N_{L/K}(b) = Σ_m [κ(B_m) : κ(A)] ord_{B_m}(b)`, the coefficient identity
behind the pushforward of principal divisors along finite maps (Fulton, Proposition 1.4(b)).
`TauCeti.ordFrac_norm_eq_finprod` states it for every nonzero `r` in `L`, multiplicatively in
`ℤᵐ⁰`, with the orders taken in arbitrary localizations `R m` of `B` at its maximal ideals (such as
the local rings of a scheme at the points of a fibre) and the residue degree read as the `A`-length
of `B ⧸ m`. The orders are transported from `B_m` to `R m` by `TauCeti.Ring.ord_ringEquiv`.
-/

public section

namespace TauCeti

variable {A K B L : Type*} [CommRing A] [Field K] [Algebra A K] [CommRing B] [Algebra A B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L]

variable (K) in
/-- For `B` integral over `A`, the fraction field `L` of `B` is spanned by `B` over any field `K`
between `A` and `L`: the `K`-span of `B` is a `K`-subalgebra, and contains the inverse of each
nonzero element of `B`, which is algebraic over `K`. -/
theorem span_range_algebraMap_eq_top [Algebra.IsIntegral A B] :
    Submodule.span K (Set.range (algebraMap B L)) = ⊤ := by
  let S : Subalgebra K L := Algebra.adjoin K (Set.range (algebraMap B L))
  have hS : Subalgebra.toSubmodule S = Submodule.span K (Set.range (algebraMap B L)) := by
    -- The range of `B → L` is closed under multiplication.
    refine Algebra.adjoin_eq_span_of_subset K fun x hx ↦ Submodule.subset_span ?_
    obtain ⟨b, rfl⟩ := MonoidHom.mem_mrange.1 <|
      (Submonoid.closure_le (S := MonoidHom.mrange (algebraMap B L : B →* L))).2
        (by rintro _ ⟨b, rfl⟩; exact MonoidHom.mem_mrange.2 ⟨b, rfl⟩) hx
    exact ⟨b, rfl⟩
  rw [← hS, eq_top_iff]
  intro x _
  obtain ⟨β, γ, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hγS : algebraMap B L γ ∈ S := Algebra.subset_adjoin ⟨γ, rfl⟩
  have hγK : IsAlgebraic K (algebraMap B L γ) :=
    (((Algebra.IsIntegral.isIntegral (R := A) γ).map (IsScalarTower.toAlgHom A B L)).tower_top
      (A := K)).isAlgebraic
  rw [div_eq_mul_inv]
  exact S.mul_mem (Algebra.subset_adjoin ⟨β, rfl⟩)
    (Subalgebra.inv_mem_of_algebraic S (x := ⟨_, hγS⟩) hγK)

variable [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsFractionRing A K]
  [Module.Finite A B]

/-- **The order of a norm is a length** (Fulton, *Intersection Theory*, Appendix A.3, first step).
Let `A` be a Noetherian domain of dimension at most one with fraction field `K`, and let `B` be a
domain finite over `A`, with fraction field `L`. For nonzero `b : B` with `B ⧸ bB` of `A`-length
`n`, the norm `N_{L/K}(b)` has order `n`. -/
theorem ordFrac_norm_eq_coe_of_length_eq {b : B} (hb : b ≠ 0) {n : ℕ}
    (hn : Module.length A (B ⧸ Ideal.span {b}) = n) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) = Multiplicative.ofAdd (n : ℤ) := by
  -- The lattice `B ⊆ L`, the image of the `A`-linear map `f`.
  let f : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap
  have hf : Function.Injective f := IsFractionRing.injective B L
  let M : Submodule A L := LinearMap.range f
  have hspan : Submodule.span K (M : Set L) = ⊤ := by
    rw [← span_range_algebraMap_eq_top K (A := A) (B := B), LinearMap.coe_range,
      AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom']
  have : Module.Finite K L := by
    classical
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := A) (M := B))
    refine ⟨⟨s.image f, ?_⟩⟩
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hy : f y ∈ Submodule.span A (f '' (s : Set B)) := by
      rw [← Submodule.map_span, hs]
      exact Submodule.mem_map_of_mem Submodule.mem_top
    rw [Finset.coe_image]
    exact Submodule.span_le_restrictScalars A K _ hy
  -- Multiplication by `b` on `L` preserves the lattice.
  let φ : L →ₗ[K] L := Algebra.lmul K L (algebraMap B L b)
  have hφM : ∀ x ∈ M, φ x ∈ M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨b * y, by simp [φ, f]⟩
  have hb' : algebraMap B L b ≠ 0 := (map_ne_zero_iff _ hf).2 hb
  have hdet : LinearMap.det φ ≠ 0 := by
    rw [← Algebra.norm_apply]
    exact (Algebra.norm_ne_zero_iff).2 hb'
  rw [Algebra.norm_apply]
  refine LinearMap.ordFrac_det_eq_coe_of_length_eq φ M ?_ hspan hφM hdet ?_
  · exact Module.Finite.iff_fg.1 (Module.Finite.range f)
  -- Under `B ≃ M`, the ideal `bB` is the image of multiplication by `b`.
  let e : B ≃ₗ[A] M := LinearEquiv.ofInjective f hf
  have he : ((Ideal.span {b}).restrictScalars A).map (e : B →ₗ[A] M) =
      LinearMap.range ((φ.restrictScalars A).restrict hφM) := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      LinearMap.mem_range, Subtype.ext_iff, LinearEquiv.coe_coe, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨f a, ⟨a, rfl⟩, by rw [LinearEquiv.ofInjective_apply]; simp [φ, f, mul_comm]⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨b * a, ⟨a, mul_comm a b⟩, by rw [LinearEquiv.ofInjective_apply]; simp [φ, f]⟩
  rw [← (Submodule.Quotient.equiv _ _ e he).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b})).length_eq, hn]

section Local

/-- Localizing `R ⧸ bR` at a prime `q` gives `R_m ⧸ b R_m`, for `m` the prime of `R` under `q`. In
particular the localization `(R ⧸ bR)_q` has length `ord_{R_m} b` over itself. -/
theorem length_localization_quotient_span_singleton {R : Type*} [CommRing R] (b : R)
    (q : Ideal (R ⧸ Ideal.span {b})) [q.IsPrime] :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Ring.ord (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))))
        (algebraMap R _ b) := by
  -- The localization `ψ : R_m → (R ⧸ bR)_q` of `R → R ⧸ bR` is surjective with kernel `b R_m`.
  let ψ := Localization.localRingHom _ q (Ideal.Quotient.mk (Ideal.span {b})) rfl
  have hψ : Function.Surjective ψ :=
    RingHom.surjective_localRingHom_of_surjective _ Ideal.Quotient.mk_surjective q
  have hker : RingHom.ker ψ = Ideal.span {algebraMap R _ b} := by
    refine (IsLocalization.ker_map (Localization.AtPrime q) (Ideal.Quotient.mk (Ideal.span {b}))
      (Ideal.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective q)).trans ?_
    rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
  let _ : Algebra (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))))
      (Localization.AtPrime q) := ψ.toAlgebra
  let e : (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))) ⧸ RingHom.ker ψ)
      ≃ₐ[Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b})))]
      Localization.AtPrime q :=
    AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hψ) fun x ↦ rfl
  rw [← Module.length_eq_of_surjective
      (S := Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b})))) hψ,
    ← e.toLinearEquiv.length_eq,
    (Ideal.quotientEquivAlgOfEq _ hker).toLinearEquiv.length_eq, Ring.ord]

/-- The residue field of `(R ⧸ bR)_q` is that of `R_m`, for `m` the prime of `R` under `q`; in
particular they have the same length over any ring `A` acting on `R`. -/
theorem _root_.Ideal.length_residueField_localization_quotient {A R : Type*} [CommRing A]
    [CommRing R] [Algebra A R] (I : Ideal R) (q : Ideal (R ⧸ I)) [q.IsPrime] :
    Module.length A (IsLocalRing.ResidueField (Localization.AtPrime q)) =
      Module.length A (IsLocalRing.ResidueField
        (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))) := by
  let ψ := Localization.localRingHom _ q (Ideal.Quotient.mk I) rfl
  have hψ : Function.Surjective ψ :=
    RingHom.surjective_localRingHom_of_surjective _ Ideal.Quotient.mk_surjective q
  let φ := IsLocalRing.ResidueField.map ψ
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun z ↦ ?_⟩
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨IsLocalRing.residue _ x, IsLocalRing.ResidueField.map_residue _ _⟩
  let e : IsLocalRing.ResidueField (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) ≃ₗ[A]
      IsLocalRing.ResidueField (Localization.AtPrime q) :=
    { RingEquiv.ofBijective φ hφ with
      map_smul' := fun a x ↦ by
        simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          RingEquiv.ofBijective_apply, Algebra.smul_def, map_mul, RingHom.id_apply]
        congr 1
        rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime (q.comap
            (Ideal.Quotient.mk I))) (IsLocalRing.ResidueField _),
          IsScalarTower.algebraMap_apply A R (Localization.AtPrime _),
          IsScalarTower.algebraMap_apply A (Localization.AtPrime q) (IsLocalRing.ResidueField _),
          IsScalarTower.algebraMap_apply A (R ⧸ I) (Localization.AtPrime q)]
        simp [φ, ψ] }
  exact e.length_eq.symm

/-- A maximal ideal of `B` containing `b` is the preimage of a maximal ideal of `B ⧸ bB`. -/
theorem exists_maximalSpectrum_comap_mk_eq {B : Type*} [CommRing B] {b : B}
    {m : MaximalSpectrum B} (hbm : b ∈ m.asIdeal) :
    ∃ q : MaximalSpectrum (B ⧸ Ideal.span {b}),
      q.asIdeal.comap (Ideal.Quotient.mk _) = m.asIdeal := by
  have hle : Ideal.span {b} ≤ m.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hbm
  exact ⟨⟨_, Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])⟩, Ideal.comap_map_mk hle⟩

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]

/-- For a domain `B` finite over a Noetherian domain `A` of dimension at most one, `B ⧸ bB` has
finite `A`-length for `b ≠ 0`: the ideal `bB` meets `A` in a nonzero element, which annihilates
`B ⧸ bB`. -/
theorem isFiniteLength_quotient_span_singleton {b : B} (hb : b ≠ 0) :
    IsFiniteLength A (B ⧸ Ideal.span {b}) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.under_ne_bot_of_integral_mem hb (Ideal.mem_span_singleton_self b)
      (Algebra.IsIntegral.isIntegral (R := A) b))
  refine isFiniteLength_of_nonZeroDivisor_mem_annihilator (x := a) ?_
    (mem_nonZeroDivisors_of_ne_zero ha0)
  rw [Module.mem_annihilator]
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ ha

/-- **The length of `B ⧸ bB` is a sum of local lengths** (Fulton, *Intersection Theory*,
Appendix A.3, second step). Let `A` be a local Noetherian domain of dimension at most one and `B`
a domain finite over `A`. For `b ≠ 0`, the Artinian ring `C = B ⧸ bB` is the product of its
localizations `C_q` at its finitely many maximal ideals, and each `C_q` has `A`-length
`length_{C_q} C_q * [κ(C_q) : κ(A)]` (Mathlib's `IsLocalRing.length_restrictScalars`); the residue
degree `[κ(C_q) : κ(A)]` is the `A`-length of `κ(C_q)`. -/
theorem length_quotient_span_singleton_eq_finsum [IsLocalRing A] {b : B} (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ᶠ q : MaximalSpectrum (B ⧸ Ideal.span {b}),
        Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
          Module.length A (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) := by
  set C := B ⧸ Ideal.span {b}
  have : IsArtinian A C :=
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (isFiniteLength_quotient_span_singleton hb)).2
  have : IsArtinianRing C := isArtinian_of_tower A inferInstance
  have := Fintype.ofFinite (MaximalSpectrum C)
  rw [((MaximalSpectrum.toPiLocalizationEquiv C).toLinearEquiv.restrictScalars A).length_eq,
    Module.length_pi_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- The maximal ideal of `C_q` lies over the maximal ideal of `A`, since `C` is integral over `A`.
  have : IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := by
    refine ((IsLocalRing.local_hom_tfae _).out 1 5).2 ?_
    have hq : (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).comap
        (algebraMap C (Localization.AtPrime q.asIdeal)) = q.asIdeal :=
      Localization.AtPrime.under_maximalIdeal
    have : q.asIdeal.IsMaximal := q.isMaximal
    rw [IsScalarTower.algebraMap_eq A C (Localization.AtPrime q.asIdeal), ← Ideal.comap_comap, hq]
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A q.asIdeal)
  rw [IsLocalRing.length_restrictScalars A (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime q.asIdeal), Module.length_eq_of_surjective
      (M := IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.residue_surjective (R := A))]

/-- **The order of a norm, local form** (Fulton, *Intersection Theory*, Appendix A.3). Let `A` be
a local Noetherian domain of dimension at most one and `B` a domain finite over `A`. For `b ≠ 0`,
`length_A (B ⧸ bB) = Σ_m ord_{B_m}(b) [κ(B_m) : κ(A)]`, the sum over the maximal ideals `m` of `B`
(only those containing `b` contribute), with the residue degree `[κ(B_m) : κ(A)]` read as the
`A`-length of `κ(B_m)`. -/
theorem length_quotient_span_singleton_eq_finsum_ord [IsLocalRing A] {b : B} (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ᶠ m : MaximalSpectrum B, Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
        Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) := by
  set G : MaximalSpectrum B → ℕ∞ := fun m ↦
    Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
      Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal))
  -- The maximal ideals of `B ⧸ bB` are those of `B` containing `b`.
  let c : MaximalSpectrum (B ⧸ Ideal.span {b}) → MaximalSpectrum B := fun q ↦
    ⟨q.asIdeal.comap (Ideal.Quotient.mk _),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  have hc : Function.Injective c := fun q q' h ↦ MaximalSpectrum.ext
    (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  have hsupp : Function.support G ⊆ Set.range c := by
    intro m hm
    have hbm : b ∈ m.asIdeal := by
      by_contra hbm
      refine hm ?_
      simp only [G, Ring.ord_of_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ b).2 hbm),
        zero_mul]
    obtain ⟨q, hq⟩ := exists_maximalSpectrum_comap_mk_eq hbm
    exact ⟨q, MaximalSpectrum.ext hq⟩
  have hG : ∑ᶠ m, G m = ∑ᶠ q, G (c q) := by
    rw [← finsum_mem_range hc, finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  rw [length_quotient_span_singleton_eq_finsum hb, hG]
  refine finsum_congr fun q ↦ ?_
  rw [length_localization_quotient_span_singleton, Ideal.length_residueField_localization_quotient]

end Local

/-- For `B` finite over a Noetherian domain `A` of dimension at most one, a nonzero `b : B` lies in
only finitely many maximal ideals of `B`: they are the maximal ideals of the Artinian ring
`B ⧸ bB`. -/
theorem finite_setOf_mem_maximalSpectrum (A : Type*) {B : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] {b : B} (hb : b ≠ 0) :
    {m : MaximalSpectrum B | b ∈ m.asIdeal}.Finite := by
  have : IsArtinian A (B ⧸ Ideal.span {b}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (isFiniteLength_quotient_span_singleton hb)).2
  have : IsArtinianRing (B ⧸ Ideal.span {b}) := isArtinian_of_tower A inferInstance
  let c : MaximalSpectrum (B ⧸ Ideal.span {b}) → MaximalSpectrum B := fun q ↦
    ⟨q.asIdeal.comap (Ideal.Quotient.mk _),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  refine (Set.finite_range c).subset fun m (hbm : b ∈ m.asIdeal) ↦ ?_
  obtain ⟨q, hq⟩ := exists_maximalSpectrum_comap_mk_eq hbm
  exact ⟨q, MaximalSpectrum.ext hq⟩

section Fraction

variable {A K B L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  (R : MaximalSpectrum B → Type*) [∀ m, CommRing (R m)] [∀ m, IsDomain (R m)]
  [∀ m, IsNoetherianRing (R m)] [∀ m, Ring.KrullDimLE 1 (R m)] [∀ m, Algebra B (R m)]
  [∀ m, IsLocalization.AtPrime (R m) m.asIdeal] [∀ m, Algebra (R m) L]
  [∀ m, IsScalarTower B (R m) L] [∀ m, IsFractionRing (R m) L]

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A] [Module.Finite A B]
  [IsDomain B] in
/-- The residue degree of a maximal ideal `m` of `B` over `A`, read as the `A`-length of
`κ(B_m)`, is the `A`-length of `B ⧸ m`. -/
theorem length_residueField_localization_eq (m : MaximalSpectrum B) :
    Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) =
      Module.length A (B ⧸ m.asIdeal) := by
  have := m.isMaximal
  exact ((IsLocalization.AtPrime.equivQuotMaximalIdeal m.asIdeal
    (Localization.AtPrime m.asIdeal)).toLinearEquiv.restrictScalars A).length_eq.symm

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A] [Module.Finite A B]
  [IsDomain B] in
/-- The order of `b ∈ B` in a localization `R m` of `B` at a maximal ideal `m`, computed on the
fraction field `L`, is its order in `B_m`. -/
theorem ordFrac_algebraMap_eq_ofAdd_ord (m : MaximalSpectrum B) {b : B} (hb : b ≠ 0) :
    Ring.ordFrac (R m) (algebraMap B L b) = Multiplicative.ofAdd
      ((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b)).toNat : ℤ) := by
  let e : Localization.AtPrime m.asIdeal ≃ₐ[B] R m :=
    IsLocalization.algEquiv m.asIdeal.primeCompl _ _
  have hy : algebraMap B (R m) b ≠ 0 := fun h ↦ hb <| IsFractionRing.injective B L <| by
    rw [IsScalarTower.algebraMap_apply B (R m) L, h, map_zero, map_zero]
  have hy' := mem_nonZeroDivisors_of_ne_zero hy
  have he : Ring.ord (R m) (algebraMap B (R m) b) =
      Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) := by
    rw [← e.commutes]
    exact Ring.ord_ringEquiv e.toRingEquiv _
  have hn : Ring.ord (R m) (algebraMap B (R m) b) =
      ((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b)).toNat : ℕ∞) := by
    rw [← he, ENat.natCast_toNat (Ring.ord_ne_top hy')]
  rw [IsScalarTower.algebraMap_apply B (R m) L, Ring.ordFrac_eq_ord (R m) hy,
    Ring.ordMonoidWithZeroHom_eq_coe (R m) hy' hn]

omit [IsFractionRing B L] [IsDomain B] in
/-- The order of `b ∈ B` is trivial at every maximal ideal of `B` not containing `b`. -/
theorem mulSupport_ordFrac_pow_subset (b : B) (d : MaximalSpectrum B → ℕ) :
    Function.mulSupport (fun m ↦ Ring.ordFrac (R m) (algebraMap B L b) ^ d m) ⊆
      {m | b ∈ m.asIdeal} := by
  intro m hm
  by_contra hbm
  refine hm ?_
  dsimp only
  rw [IsScalarTower.algebraMap_apply B (R m) L, Ring.ordFrac_of_isUnit (K := L)
    ((IsLocalization.AtPrime.isUnit_to_map_iff (R m) m.asIdeal b).2 hbm), one_pow]

/-- **The order of a norm, multiplicative form** (Fulton, *Intersection Theory*, Appendix A.3).
Let `A` be a local Noetherian domain of dimension at most one with fraction field `K`, `B` a domain
finite over `A` with fraction field `L`, and `R m` a localization of `B` at each maximal ideal
`m`. For `b ≠ 0` in `B`, `ord_A N_{L/K}(b) = Σ_m [B ⧸ m : κ(A)] ord_{R m}(b)`, written
multiplicatively in `ℤᵐ⁰`, with the residue degree read as the `A`-length of `B ⧸ m`. -/
theorem ordFrac_norm_algebraMap_eq_finprod {b : B} (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      ∏ᶠ m, Ring.ordFrac (R m) (algebraMap B L b) ^ (Module.length A (B ⧸ m.asIdeal)).toNat := by
  classical
  set S := (finite_setOf_mem_maximalSpectrum A hb).toFinset
  have hfin : Module.length A (B ⧸ Ideal.span {b}) ≠ ⊤ :=
    Module.length_ne_top_iff.2 (isFiniteLength_quotient_span_singleton hb)
  -- The local lengths of `B ⧸ bB` vanish away from the maximal ideals containing `b`.
  have hlen := length_quotient_span_singleton_eq_finsum_ord (A := A) hb
  rw [finsum_eq_sum_of_support_subset _ (s := S) fun m hm ↦ by
    simp only [S, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    by_contra hbm
    exact hm (by
      dsimp only
      rw [Ring.ord_of_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ b).2 hbm), zero_mul])]
    at hlen
  have hS : ∀ m ∈ S, Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
      Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) ≠ ⊤ :=
    ENat.sum_ne_top.1 (hlen ▸ hfin)
  rw [ordFrac_norm_eq_coe_of_length_eq (K := K) (L := L) hb (ENat.natCast_toNat hfin).symm,
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (by
      simp only [S, Set.Finite.coe_toFinset]; exact mulSupport_ordFrac_pow_subset R b _),
    hlen, ENat.toNat_sum hS]
  simp only [ordFrac_algebraMap_eq_ofAdd_ord R _ hb, ENat.toNat_mul,
    length_residueField_localization_eq, ← WithZero.coe_pow, ← ofAdd_nsmul, Nat.cast_sum,
    Nat.cast_mul, nsmul_eq_mul, mul_comm, ofAdd_sum]
  exact map_prod (WithZero.coeMonoidHom (α := Multiplicative ℤ)) _ _

/-- **The order of a norm** (Fulton, *Intersection Theory*, Appendix A.3). Let `A` be a local
Noetherian domain of dimension at most one with fraction field `K`, `B` a domain finite over `A`
with fraction field `L`, and `R m` a localization of `B` at each maximal ideal `m`. For `r ≠ 0`
in `L`, `ord_A N_{L/K}(r) = Σ_m [B ⧸ m : κ(A)] ord_{R m}(r)`, written multiplicatively in `ℤᵐ⁰`,
with the residue degree read as the `A`-length of `B ⧸ m`. This is the coefficient identity behind
the pushforward of principal divisors along finite maps (Fulton, Proposition 1.4(b)). -/
theorem ordFrac_norm_eq_finprod {r : L} (hr : r ≠ 0) :
    Ring.ordFrac A (Algebra.norm K r) =
      ∏ᶠ m, Ring.ordFrac (R m) r ^ (Module.length A (B ⧸ m.asIdeal)).toNat := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := B) r
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb0 : b ≠ 0 := by rintro rfl; simp at hr
  set d : MaximalSpectrum B → ℕ := fun m ↦ (Module.length A (B ⧸ m.asIdeal)).toNat
  have hfin (x : B) (hx : x ≠ 0) :
      Function.HasFiniteMulSupport fun m ↦ Ring.ordFrac (R m) (algebraMap B L x) ^ d m :=
    (finite_setOf_mem_maximalSpectrum A hx).subset (mulSupport_ordFrac_pow_subset R x d)
  have hN : Algebra.norm K (algebraMap B L c)⁻¹ = (Algebra.norm K (algebraMap B L c))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by
      rw [← map_mul, inv_mul_cancel₀ (by simpa using hc0), map_one])
  simp_rw [div_eq_mul_inv, map_mul, hN, map_inv₀, mul_pow, inv_pow]
  rw [finprod_mul_distrib (hfin b hb0) ?_, finprod_inv_distrib,
    ordFrac_norm_algebraMap_eq_finprod R hb0, ordFrac_norm_algebraMap_eq_finprod R hc0]
  exact (hfin c hc0).inv

end Fraction

end TauCeti
