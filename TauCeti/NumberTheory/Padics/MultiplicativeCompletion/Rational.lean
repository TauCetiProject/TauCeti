/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Tower
import TauCeti.LinearAlgebra.Dimension.Localization
import TauCeti.NumberTheory.LocalField.DeepUnits.Basic
import TauCeti.NumberTheory.LocalField.UnitFiltration.GaloisAction
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Finite
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.FreeQuotient

/-!
# The rationalization of the completed multiplicative module

For a finite extension `L` of `ℚ_[p]`, the completed multiplicative module
`A(L) = lim_m Lˣ/(Lˣ)^(p^m)` of `TauCeti.padicCompletionUnits` has `ℤ_p`-rank `[L : ℚ_p] + 1`
(`TauCeti.finrank_padicCompletionUnits`), so its rationalization `A(L) ⊗[ℤ_p] ℚ_p` is a
`ℚ_p`-vector space of dimension `[L : ℚ_p] + 1`. This file records that dimension and determines
the Galois structure of the rationalization.

Over a finite Galois layer `L/K` of `p`-adic fields with group `G = Gal(L/K)` and
`N = [K : ℚ_p]`, the rationalization is the `ℚ_p[G]`-module `ℚ_p[G]^N ⊕ ℚ_p` (NSW (7.4.4)(i)); as
a `ℤ_p[G]`-module it is written `(ℤ_p[G]^N × ℤ_p[G] ⧸ I_G) ⊗[ℤ_p] ℚ_p`, with the trivial module
`ℤ_p[G] ⧸ I_G` in place of `ℚ_p` so that no second module structure is installed on `ℚ_p`
(`TauCeti.nonempty_padicCompletionUnits_tensorRat_linearEquiv`).

The decomposition comes from an integral lattice of full rank. A normal basis `σ ↦ σ α` of `L/K`
and a `ℚ_p`-basis `b` of `K` give the `ℚ_p`-basis `b_k σ(α)` of `L`; choose deep units `u_k`
whose logarithms are nonzero `ℚ_p`-multiples of `b_k α`. The logarithm commutes with `G`, so the
logarithms of the conjugates `σ(u_k)` are linearly independent over `ℚ_p`, and the classes of the
`σ(u_k)` and of `p` are linearly independent over `ℤ_p` in `A(L)`
(`TauCeti.linearIndependent_padicCompletionUnitsOf`). Hence the `ℤ_p[G]`-linear map
`ℤ_p[G]^N × ℤ_p[G] ⧸ I_G → A(L)` sending the `k`-th basis vector to the class of `u_k` and `1`
to the class of `p`, which is fixed by `G`, is injective. Both sides have `ℤ_p`-rank
`N · [L : K] + 1`, so it becomes an isomorphism after tensoring with `ℚ_p`.

The dimension count is also where the Galois hypothesis enters: the right side has dimension
`N · #G + 1`, the left `[L : ℚ_p] + 1 = N · [L : K] + 1`, and these agree exactly when
`#Aut_K(L) = [L : K]`. So over a layer whose automorphism group is smaller than its degree, no
`ℤ_p[G]`-linear isomorphism between the two sides exists
(`TauCeti.not_nonempty_padicCompletionUnits_tensorRat_linearEquiv_of_card_lt`). Finiteness of
`Aut_K(L)` is therefore not a substitute for `L/K` being Galois in the decomposition; the
non-Galois cubic `ℚ₅(∛5)` of `TauCeti.NonGaloisCubic` is an explicit instance.

## Main results

* `TauCeti.finrank_padicCompletionUnits_tensorRat`: `A(L) ⊗[ℤ_p] ℚ_p` has `ℤ_p`-rank, hence
  `ℚ_p`-dimension, `[L : ℚ_p] + 1`.
* `TauCeti.nonempty_padicCompletionUnits_tensorRat_linearEquiv`: the rational decomposition
  `A(L) ⊗ ℚ_p ≃ (ℤ_p[G]^N × ℤ_p[G] ⧸ I_G) ⊗ ℚ_p` of `ℤ_p[G]`-modules over a finite Galois layer
  `L/K` of `p`-adic fields, that is `A(L) ⊗ ℚ_p ≃ ℚ_p[G]^N ⊕ ℚ_p`.
* `TauCeti.not_nonempty_padicCompletionUnits_tensorRat_linearEquiv_of_card_lt`: over a finite
  layer `L/K` of `p`-adic fields with `#Aut_K(L) < [L : K]`, `A(L) ⊗ ℚ_p` is not
  `ℤ_p[Aut_K(L)]`-isomorphic to `(ℤ_p[Aut_K(L)]^N × ℤ_p[Aut_K(L)] ⧸ I) ⊗ ℚ_p`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.4.4) and the proof of
  (7.4.1).
* K. Iwasawa, *On Galois groups of local fields*, Trans. Amer. Math. Soc. 80 (1955), 448–469.
-/

public section

namespace TauCeti

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

section Dimension

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L]

/-- **The dimension of the rationalization of `A(L)`.** For a finite extension `L` of `ℚ_[p]`,
the `ℤ_p`-rank of `A(L) ⊗[ℤ_p] ℚ_p` is `[L : ℚ_p] + 1`. Since `ℤ_p` acts on this `ℚ_p`-vector
space through `ℚ_p`, this is also its `ℚ_p`-dimension. -/
theorem finrank_padicCompletionUnits_tensorRat :
    Module.finrank ℤ_[p] (Additive ↑(padicCompletionUnits p L) ⊗[ℤ_[p]] ℚ_[p]) =
      Module.finrank ℚ_[p] L + 1 := by
  rw [IsLocalization.finrank_tensorProduct (nonZeroDivisors ℤ_[p]) ℚ_[p] le_rfl,
    finrank_padicCompletionUnits]

end Dimension

/-! ### The rational decomposition -/

section Decomposition

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FinitePadicExtension L p]
  {K : Type*} [Field K] [Algebra K L] [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K L] [IsGalois K L]

variable (L K) in
/-- **An integral lattice of full rank in `A(L)`.** Over a finite Galois layer `L/K` of a finite
extension `L` of `ℚ_p`, with `G = Gal(L/K)` and `N = [K : ℚ_p]`, there is an injective
`ℤ_p[G]`-linear map `ℤ_p[G]^N × ℤ_p[G] ⧸ I_G → A(L)`: the `k`-th basis vector goes to the class of
a deep unit `u_k` whose logarithm is a nonzero multiple of `b_k α`, for a `ℚ_p`-basis `b` of `K`
and a normal basis generator `α` of `L/K`, and `1` goes to the class of `p`. -/
private theorem exists_injective_linearMap_padicCompletionUnits :
    ∃ Φ : ((Fin (Module.finrank ℚ_[p] K) → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) ×
        (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸
          RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))))
        →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L),
      Function.Injective Φ := by
  have hi : absoluteRamificationIndex L p < (p - 1) * (absoluteRamificationIndex L p + 1) :=
    (Nat.lt_succ_self _).trans_le
      (Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
  have hp0 : (p : L) ≠ 0 := by
    have := FinitePadicExtension.charZero L p
    exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have : Module.Finite ℚ_[p] K := .left ℚ_[p] K L
  have : Module.Finite K L := .right ℚ_[p] K L
  -- Instance search for `Module.Free ℚ_[p] K` times out through the algebra instances on `L`.
  have : Module.Free ℚ_[p] K := .of_divisionRing ℚ_[p] K
  set b := Module.finBasis ℚ_[p] K
  set nb := IsGalois.normalBasis K L
  -- Deep units `u k` whose logarithms are nonzero multiples of `b k • α` for the normal basis
  -- generator `α = nb 1`, and their conjugates `v (k, σ) = σ (u k)`.
  choose u hu c hc hlog using fun k ↦ exists_mem_unitFiltration_log_eq_smul hi (b k • nb 1)
  set v : Fin (Module.finrank ℚ_[p] K) × (L ≃ₐ[K] L) → Lˣ :=
    fun j ↦ Units.map j.2.toRingEquiv.toMonoidHom (u j.1)
  have hv (j) : v j ∈ unitFiltration L (absoluteRamificationIndex L p + 1) :=
    (j.2.restrictScalars ℚ_[p]).unitsMap_mem_unitFiltration_iff.mpr (hu j.1)
  have hvlog (j) : NormedSpace.log (v j : L) = c j.1 • (b.smulTower nb) j := by
    have h := (j.2.restrictScalars ℚ_[p]).map_log_of_mem_unitFiltration_one p
      (unitFiltration_antitone (Nat.succ_le_succ (Nat.zero_le _)) (hu j.1))
    rw [hlog, map_smul, AlgEquiv.restrictScalars_apply, AlgEquiv.restrictScalars_apply,
      map_smul] at h
    rw [Module.Basis.smulTower_apply, IsGalois.normalBasis_apply, h, Units.coe_map]
    simp
  have hind : LinearIndependent ℚ_[p] fun j ↦ NormedSpace.log (v j : L) := by
    convert (b.smulTower nb).linearIndependent.units_smul
      (fun j ↦ Units.mk0 (c j.1) (hc j.1)) using 1
    funext j
    rw [hvlog, Pi.smul_apply', Units.smul_mk0]
  -- The classes of `p` and of the `σ (u k)` are linearly independent over `ℤ_p` in `A(L)`.
  set ϖ : Lˣ := Units.mk0 (p : L) hp0
  have hlin := linearIndependent_padicCompletionUnitsOf p hi hv hind (ϖ := ϖ) rfl
  -- The class of `p` is fixed by `G`, so `ℤ_p[G]` acts on it through the augmentation.
  set y : Additive ↑(padicCompletionUnits p L) := Additive.ofMul (padicCompletionUnitsOf p L ϖ)
  have hy (r : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) :
      r • y = MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L) r • y :=
    r.smul_padicCompletionUnitsOf_of_forall_eq p fun σ ↦ Units.ext (by simp [ϖ])
  have hI : RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L)) ≤
      LinearMap.ker (LinearMap.toSpanSingleton _ _ y) := fun r hr ↦ by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, hy, RingHom.mem_ker.mp hr, zero_smul]
  -- The lattice map sends the `k`-th basis vector of `ℤ_p[G]^N` to the class of `u k`, and the
  -- trivial module `ℤ_p[G] ⧸ I_G` onto the span of the class of `p`.
  refine ⟨(∑ k, (LinearMap.toSpanSingleton _ _
      (Additive.ofMul (padicCompletionUnitsOf p L (u k)))).comp (LinearMap.proj k)).coprod
    (Submodule.liftQ _ _ hI), ?_⟩
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, q⟩ h
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [LinearMap.coprod_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.toSpanSingleton_apply, Submodule.liftQ_apply, hy] at h
  rw [Finset.sum_congr rfl fun k _ ↦ (a k).smul_padicCompletionUnitsOf p (u k)] at h
  -- Read off the coefficients of the relation against the independent classes.
  have h0 := Fintype.linearIndependent_iff.mp hlin
    (Option.elim · (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L) r) fun j ↦ (a j.1).coeff j.2)
    (by rw [Fintype.sum_option, Fintype.sum_prod_type, add_comm]; simpa [v] using h)
  exact Prod.ext (funext fun k ↦ MonoidAlgebra.ext (Finsupp.ext fun σ ↦ h0 (some (k, σ))))
    ((Submodule.Quotient.mk_eq_zero _).mpr (RingHom.mem_ker.mpr (h0 none)))

end Decomposition

/-- **The rational decomposition of `A(L)`** (NSW (7.4.4)(i)). Let `L/K` be a finite Galois layer
of `p`-adic fields, with `L` finite over `ℚ_p`, group `G = Gal(L/K)`, `N = [K : ℚ_p]` and
augmentation ideal `I_G`. Then the rationalization `A(L) ⊗[ℤ_p] ℚ_p` of the completed
multiplicative module is isomorphic to `(ℤ_p[G]^N × ℤ_p[G] ⧸ I_G) ⊗[ℤ_p] ℚ_p` as a left
`ℤ_p[G]`-module, that is, `A(L) ⊗ ℚ_p ≃ ℚ_p[G]^N ⊕ ℚ_p`: `N` copies of the regular representation
and one trivial representation. -/
theorem nonempty_padicCompletionUnits_tensorRat_linearEquiv
    {L : Type*} [Field L] {K : Type*} [Field K] [Algebra K L] [Algebra ℚ_[p] L]
    [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K L] [IsGalois K L] :
    Nonempty ((Additive ↑(padicCompletionUnits p L) ⊗[ℤ_[p]] ℚ_[p])
      ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      (((Fin (Module.finrank ℚ_[p] K) → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) ×
        (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸
          RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L)))) ⊗[ℤ_[p]] ℚ_[p])) := by
  have := Module.Finite.right ℚ_[p] K L
  -- Give `L` the local-field structure extending that of `ℚ_[p]`; the statement does not see it.
  let _ := finiteExtensionValuativeRel ℚ_[p] L
  let _ := finiteExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_valuativeExtension ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  obtain ⟨Φ, hΦ⟩ := exists_injective_linearMap_padicCompletionUnits p L K
  have := module_finite_padicCompletionUnits_padicInt (p := p) (L := L) (by
    have := FinitePadicExtension.charZero L p
    exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  -- Both sides have `ℤ_p`-rank `N · [L : K] + 1 = [L : ℚ_p] + 1`.
  have hrank : Module.finrank ℤ_[p] ((Fin (Module.finrank ℚ_[p] K) →
      MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) × (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸
        RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L)))) =
      Module.finrank ℤ_[p] (Additive ↑(padicCompletionUnits p L)) := by
    have : Module.Free ℚ_[p] K := .of_divisionRing ℚ_[p] K
    have : Module.Free K L := .of_divisionRing K L
    rw [MonoidAlgebra.finrank_pi_prod_quotient_ker_augmentation, finrank_padicCompletionUnits,
      ← Module.finrank_mul_finrank ℚ_[p] K L, IsGalois.card_aut_eq_finrank]
  exact ⟨(LinearEquiv.ofBijective _
    (IsFractionRing.rTensor_bijective_of_injective_of_finrank_eq ℚ_[p] Φ hΦ hrank)).symm⟩

/-- **Rejection test for the Galois hypothesis of the rational decomposition.** Let `L/K` be a
finite layer of `p`-adic fields whose automorphism group `Aut_K(L)` has fewer elements than the
degree `[L : K]`, as happens for a non-Galois layer. Then `A(L) ⊗ ℚ_p` is **not**
`ℤ_p[Aut_K(L)]`-isomorphic to `(ℤ_p[Aut_K(L)]^N × ℤ_p[Aut_K(L)] ⧸ I) ⊗ ℚ_p`, for `N = [K : ℚ_p]`
and `I` the augmentation ideal: the left side has `ℚ_p`-dimension `[L : ℚ_p] + 1 = N · [L : K] + 1`
and the right side `N · #Aut_K(L) + 1`. So the Galois hypothesis of the decomposition
`A(L) ⊗ ℚ_p ≃ ℚ_p[Gal(L/K)]^N ⊕ ℚ_p` cannot be weakened to finiteness of the automorphism
group. -/
theorem not_nonempty_padicCompletionUnits_tensorRat_linearEquiv_of_card_lt
    {L : Type*} [Field L] {K : Type*} [Field K] [Algebra K L] [Algebra ℚ_[p] L]
    [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K L]
    (h : Nat.card (L ≃ₐ[K] L) < Module.finrank K L) :
    ¬ Nonempty ((Additive ↑(padicCompletionUnits p L) ⊗[ℤ_[p]] ℚ_[p])
      ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      (((Fin (Module.finrank ℚ_[p] K) → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) ×
        (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸
          RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L)))) ⊗[ℤ_[p]] ℚ_[p])) := by
  rintro ⟨e⟩
  have := Module.Finite.left ℚ_[p] K L
  have := Module.Finite.right ℚ_[p] K L
  have hfinrank := (e.restrictScalars ℤ_[p]).finrank_eq
  rw [finrank_padicCompletionUnits_tensorRat,
    IsLocalization.finrank_tensorProduct (nonZeroDivisors ℤ_[p]) ℚ_[p] le_rfl,
    MonoidAlgebra.finrank_pi_prod_quotient_ker_augmentation,
    ← Module.finrank_mul_finrank ℚ_[p] K L] at hfinrank
  have hpos : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have := Nat.mul_lt_mul_of_pos_left h hpos
  omega

end TauCeti
