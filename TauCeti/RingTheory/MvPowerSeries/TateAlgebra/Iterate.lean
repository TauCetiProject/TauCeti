/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.TateAlgebra
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

/-!
# Iteration of Gauss-normed restricted series in one variable

For positive polyradii `c : Option σ → ℝ`, separating the variable `none` identifies restricted
series in `Option σ` at the polyradii `c` with univariate series restricted at the radius
`c none`, whose coefficients are restricted series in `σ` at the polyradii `c ∘ some`:

```text
R{X/c} ≅ R{Y/(c ∘ some)}{T/c none}.
```

The comparison is an `R`-algebra equivalence preserving the Gauss norms. The series rings are
complete when the coefficient ring is complete. It allows one-variable Weierstrass division and
preparation over the ring of restricted series in the remaining variables, at every positive
polyradius and in particular for the unit-radius Tate algebra.

The construction restricts Mathlib's `MvPowerSeries.optionEquivLeft`; restrictedness of the
coefficient slices and convergence of their weighted Gauss norms are both required. Merely
requiring each slice to be restricted would not characterize multivariate restricted series.
For two arbitrary families of variables, the analogous comparison into multivariate series is
`TauCeti.MvPowerSeries.restrictedSumEquiv`. The comparison `MvPowerSeries.restrictedSplitEquiv`
first reindexes by an equivalence `e : ι ≃ Option σ`, so that the chosen variable
`e.symm none` is separated. In particular, `finSuccEquiv n` separates variable `0` in
`Fin (n + 1)`.

## Main results

* `MvPowerSeries.norm_coeff_coeff_optionEquivLeft_mul_prod_mul_pow`: the weighted norms of the
  coefficients of the slices, weighted again by `c none`, are the weighted norms at `c`.
* `MvPowerSeries.isRestricted_coeff_optionEquivLeft`: the coefficient slices of a restricted
  series in `Option σ` are restricted in `σ`.
* `MvPowerSeries.restrictedOptionEquiv`: the algebra isomorphism
  `R{X/c} ≃ₐ[R] R{Y/(c ∘ some)}{T/c none}`, with its coefficients
  `MvPowerSeries.coeff_restrictedOptionEquiv` and the inverse
  `MvPowerSeries.coe_restrictedOptionEquiv_symm`. It sends scalars to scalars by
  `AlgEquiv.commutes`.
* `MvPowerSeries.coeff_restrictedOptionEquiv_eq_zero_iff`: a coefficient of the iterated series
  vanishes exactly when every monomial with that exponent of the separated variable does.
* `MvPowerSeries.coe_restrictedOptionEquiv_X_none` and
  `MvPowerSeries.coe_restrictedOptionEquiv_X_some`: it sends the separated variable to the
  univariate variable, and the remaining variables to constants.
* `MvPowerSeries.norm_restrictedOptionEquiv` and `MvPowerSeries.isometry_restrictedOptionEquiv`:
  it preserves the Gauss norms.
* `MvPowerSeries.isRestricted_of_map_subtype_eq_optionEquivLeft`: transporting restriction from
  constant radius `r` to an iterated series with coefficient radius `ρ ≤ r`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.1.1 and 5.2.1.
* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), §1.3, for restricted series at arbitrary real radii.
-/

public section

namespace MvPowerSeries

open Filter
open scoped Topology

variable {σ R : Type*} {c : Option σ → ℝ}

/-- Separating the variable `none` with `MvPowerSeries.optionEquivLeft`, the weighted norm at the
polyradii `c ∘ some` of the coefficient at `t` of the `n`-th coefficient slice, weighted again by
`c none ^ n`, is the weighted norm at the polyradii `c` of the coefficient of `f` at
`t.optionElim n`. -/
theorem norm_coeff_coeff_optionEquivLeft_mul_prod_mul_pow [CommSemiring R] [Norm R]
    (f : MvPowerSeries (Option σ) R) (n : ℕ) (t : σ →₀ ℕ) :
    ‖coeff t (PowerSeries.coeff n (optionEquivLeft σ R f))‖ *
        t.prod (fun i k ↦ c (some i) ^ k) * c none ^ n =
      ‖coeff (t.optionElim n) f‖ * (t.optionElim n).prod (c · ^ ·) := by
  rw [coeff_coeff_optionEquivLeft, Finsupp.prod_pow_optionElim]
  ring

variable [NormedCommRing R]

/-- Each coefficient slice obtained by separating one variable is restricted. Only the radius of
the separated variable needs to be positive. -/
theorem isRestricted_coeff_optionEquivLeft (hc : 0 < c none) {f : MvPowerSeries (Option σ) R}
    (hf : IsRestricted c f) (n : ℕ) :
    IsRestricted (fun i ↦ c (some i)) (PowerSeries.coeff n (optionEquivLeft σ R f)) := by
  rw [← isRestrictedFamily_coeff_iff]
  simpa only [coeff_coeff_optionEquivLeft] using
    ((isRestrictedFamily_coeff_iff f).mpr hf).comp_optionElim hc n

variable [IsUltrametricDist R] [∀ i, Fact (0 < c i)]

local notation "Inner" => IsRestricted.subring (R := R) (fun i : σ ↦ c (some i))
local notation "Flat" => IsRestricted.subring (R := R) c
local notation "Iter" => PowerSeries.IsRestricted.subring (R := Inner) (c none)

/-- The coefficient slices, regarded as a formal univariate series over the restricted subring. -/
private noncomputable def restrictedOptionSeries (f : Flat) : PowerSeries Inner :=
  PowerSeries.mk fun n ↦
    ⟨PowerSeries.coeff n (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)),
      isRestricted_coeff_optionEquivLeft Fact.out f.2 n⟩

private theorem coeff_restrictedOptionSeries (f : Flat) (n : ℕ) :
    (PowerSeries.coeff (R := Inner) n (restrictedOptionSeries f) : MvPowerSeries σ R) =
      PowerSeries.coeff n (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)) := by
  simp [restrictedOptionSeries]

private theorem isRestricted_restrictedOptionSeries (f : Flat) :
    PowerSeries.IsRestricted (c none) (restrictedOptionSeries f) := by
  have hpos (n : ℕ) : 0 < c none ^ n := pow_pos Fact.out n
  rw [PowerSeries.isRestricted_iff]
  refine tendsto_order.mpr ⟨fun _ hb ↦ .of_forall fun n ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (hpos n).le), fun ε hε ↦ ?_⟩
  -- only finitely many weighted coefficients of `f` reach `ε / 2`; the exponents of `none` in
  -- these are the only ones at which the weighted Gauss norm of the slice can reach `ε`
  have hbad :
      {t | ε / 2 ≤ ‖coeff t (f : MvPowerSeries (Option σ) R)‖ * t.prod (c · ^ ·)}.Finite := by
    simpa [eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds (half_pos hε))
  rw [eventually_cofinite]
  refine (hbad.image fun t ↦ t none).subset fun n hn ↦ ?_
  by_contra hnn
  refine (half_lt_self hε).not_ge ((not_lt.mp hn).trans ?_)
  rw [← le_div_iff₀ (hpos n), MvPowerSeries.norm_le_iff
    (div_nonneg (half_pos hε).le (hpos n).le)]
  intro t
  rw [le_div_iff₀ (hpos n), coeff_restrictedOptionSeries,
    norm_coeff_coeff_optionEquivLeft_mul_prod_mul_pow]
  by_contra hlt
  exact hnn ⟨t.optionElim n, (not_le.mp hlt).le, Finsupp.optionElim_apply_none n t⟩

/-- Flattening a restricted series over a restricted-series coefficient ring is restricted. -/
private theorem isRestricted_optionEquivLeft_symm (g : Iter) :
    IsRestricted c ((optionEquivLeft σ R).symm
      (PowerSeries.map (Inner).subtype (g : PowerSeries Inner))) := by
  classical
  set h := (optionEquivLeft σ R).symm (PowerSeries.map (Inner).subtype (g : PowerSeries Inner))
  have hpos (n : ℕ) : 0 < c none ^ n := pow_pos Fact.out n
  have hslice (n : ℕ) : PowerSeries.coeff n (optionEquivLeft σ R h) =
      (PowerSeries.coeff (R := Inner) n (g : PowerSeries Inner) : MvPowerSeries σ R) := by
    simp [h]
  refine tendsto_order.mpr ⟨fun _ hb ↦ .of_forall fun t ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (MvPowerSeries.prod_pow_pos t).le), fun ε hε ↦ ?_⟩
  -- a weighted coefficient of `h` reaching `ε` comes from one of the finitely many coefficients
  -- of `g` whose weighted norm reaches `ε`, and from one of the finitely many coefficients of
  -- that slice whose weighted norm, weighted again, reaches `ε`
  have hg : Tendsto (fun n ↦ ‖PowerSeries.coeff (R := Inner) n (g : PowerSeries Inner)‖ *
      c none ^ n) cofinite (𝓝 0) := (PowerSeries.isRestricted_iff _ _).mp g.2
  have houter : {n | ε ≤ ‖PowerSeries.coeff (R := Inner) n (g : PowerSeries Inner)‖ *
      c none ^ n}.Finite := by
    simpa [eventually_cofinite, not_lt] using hg.eventually (gt_mem_nhds hε)
  have hinner (n : ℕ) : {t | ε / c none ^ n ≤ ‖coeff t
      (PowerSeries.coeff (R := Inner) n (g : PowerSeries Inner) : MvPowerSeries σ R)‖ *
        t.prod (fun i k ↦ c (some i) ^ k)}.Finite := by
    simpa [eventually_cofinite, not_lt] using
      (PowerSeries.coeff n (g : PowerSeries Inner)).2.eventually
        (gt_mem_nhds (div_pos hε (hpos n)))
  rw [eventually_cofinite]
  refine (houter.biUnion fun n _ ↦ (hinner n).image fun t ↦ t.optionElim n).subset
    fun t ht ↦ ?_
  have ht' : ε ≤ ‖coeff (t.some.optionElim (t none)) h‖ *
      (t.some.optionElim (t none)).prod (c · ^ ·) := by
    rw [Finsupp.optionElim_some]
    exact not_lt.mp ht
  rw [← norm_coeff_coeff_optionEquivLeft_mul_prod_mul_pow, hslice] at ht'
  have hle := MvPowerSeries.norm_coeff_mul_prod_le
    (PowerSeries.coeff (t none) (g : PowerSeries Inner)) t.some
  refine Set.mem_biUnion (x := t none) ?_ ⟨t.some, ?_, Finsupp.optionElim_some t⟩
  · exact ht'.trans (mul_le_mul_of_nonneg_right hle (hpos _).le)
  · rw [Set.mem_ofPred_eq, div_le_iff₀ (hpos _)]
    exact ht'

/-- Flattening the iterated restricted-series algebra into the multivariate restricted-series
algebra. -/
private noncomputable def restrictedOptionFlatten : Iter →ₐ[R] Flat where
  toRingHom := (((optionEquivLeft σ R).symm.toRingHom.comp (PowerSeries.map (Inner).subtype)).comp
    (Iter).subtype).codRestrict _ isRestricted_optionEquivLeft_symm
  commutes' r := by
    apply Subtype.ext
    apply (optionEquivLeft σ R).injective
    simp

private theorem restrictedOptionFlatten_bijective :
    Function.Bijective (restrictedOptionFlatten (σ := σ) (R := R) (c := c)) := by
  refine ⟨fun g h heq ↦ Subtype.ext ?_, fun f ↦ ⟨⟨restrictedOptionSeries f,
    isRestricted_restrictedOptionSeries f⟩,
    Subtype.ext ((optionEquivLeft σ R).injective ?_)⟩⟩
  · exact PowerSeries.map_injective (Inner).subtype Subtype.val_injective
      ((optionEquivLeft σ R).symm.injective (congrArg Subtype.val heq))
  · ext n : 1
    simp [restrictedOptionFlatten, coeff_restrictedOptionSeries]

/-- **Restricted series in `Option σ` are univariate restricted series over restricted series
in `σ`.** For positive polyradii `c`, this is the algebra isomorphism
`R{X/c} ≃ₐ[R] R{Y/(c ∘ some)}{T/c none}` induced by `MvPowerSeries.optionEquivLeft`. No
completeness of `R` and no finiteness of the variable type is needed. -/
noncomputable def restrictedOptionEquiv : Flat ≃ₐ[R] Iter :=
  (AlgEquiv.ofBijective _ (restrictedOptionFlatten_bijective (σ := σ) (R := R) (c := c))).symm

private theorem restrictedOptionEquiv_symm_apply (g : Iter) :
    restrictedOptionEquiv.symm g = restrictedOptionFlatten g := by
  rw [restrictedOptionEquiv, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply]

/-- Flattening the comparison recovers Mathlib's inverse formal-series comparison. -/
@[simp]
theorem coe_restrictedOptionEquiv_symm (g : Iter) :
    (restrictedOptionEquiv.symm g : MvPowerSeries (Option σ) R) =
      (optionEquivLeft σ R).symm (PowerSeries.map (Inner).subtype (g : PowerSeries Inner)) := by
  rw [restrictedOptionEquiv_symm_apply]
  simp [restrictedOptionFlatten]

/-- The iterated series has exactly the coefficient slices of Mathlib's formal-series comparison. -/
@[simp]
theorem coeff_restrictedOptionEquiv (f : Flat) (n : ℕ) :
    (PowerSeries.coeff (R := Inner) n (restrictedOptionEquiv f : PowerSeries Inner) :
      MvPowerSeries σ R) =
      PowerSeries.coeff n (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)) := by
  have h := congrArg (fun a : Flat ↦ PowerSeries.coeff n (optionEquivLeft σ R
    (a : MvPowerSeries (Option σ) R))) ((restrictedOptionEquiv (c := c)).symm_apply_apply f)
  rw [coe_restrictedOptionEquiv_symm, AlgEquiv.apply_symm_apply, PowerSeries.coeff_map] at h
  exact h

/-- The coefficient of degree `n` of the iterated series vanishes exactly when `f` has no
monomial in which the separated variable occurs with exponent `n`. -/
theorem coeff_restrictedOptionEquiv_eq_zero_iff (f : Flat) (n : ℕ) :
    PowerSeries.coeff (R := Inner) n (restrictedOptionEquiv f : PowerSeries Inner) = 0 ↔
      ∀ t : Option σ →₀ ℕ, t none = n → coeff t (f : MvPowerSeries (Option σ) R) = 0 := by
  rw [← Subtype.coe_inj, coeff_restrictedOptionEquiv, ZeroMemClass.coe_zero,
    MvPowerSeries.ext_iff]
  simp only [coeff_coeff_optionEquivLeft, map_zero]
  refine ⟨fun h t ht ↦ ?_, fun h u ↦ h _ (Finsupp.optionElim_apply_none n u)⟩
  have h' := h t.some
  rwa [← ht, Finsupp.optionElim_some] at h'

/-- The iterated series vanishes in all degrees at least `s` exactly when the separated
variable has exponent less than `s` in every nonzero monomial. -/
theorem forall_coeff_restrictedOptionEquiv_eq_zero_iff (f : Flat) (s : ℕ) :
    (∀ m, s ≤ m → PowerSeries.coeff m (restrictedOptionEquiv f : PowerSeries Inner) = 0) ↔
      ∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (f : MvPowerSeries (Option σ) R) = 0 := by
  constructor
  · exact fun h t ht ↦
      (coeff_restrictedOptionEquiv_eq_zero_iff f (t none)).mp (h _ ht) t rfl
  · exact fun h m hm ↦
      (coeff_restrictedOptionEquiv_eq_zero_iff f m).mpr fun t ht ↦ h t (ht ▸ hm)

/-- The comparison is determined by its formal series: the image of `f` is the image of `f`
under `MvPowerSeries.optionEquivLeft`, with coefficients regarded as restricted series. -/
@[simp]
theorem map_subtype_restrictedOptionEquiv (f : Flat) :
    PowerSeries.map (Inner).subtype (restrictedOptionEquiv f : PowerSeries Inner) =
      optionEquivLeft σ R (f : MvPowerSeries (Option σ) R) := by
  ext n : 1
  simp

/-- The split polyradius on `Option σ`: radius `r` in the separated variable and
radius `ρ` in the remaining variables. -/
abbrev splitRadius (r ρ : ℝ) : Option σ → ℝ
  | none => r
  | some _ => ρ

/-- For `ρ ≤ r`, the split polyradius is bounded below by `ρ`. -/
theorem le_splitRadius {r ρ : ℝ} (h : ρ ≤ r) : ∀ i : Option σ, ρ ≤ splitRadius r ρ i
  | none => h
  | some _ => le_rfl

/-- For `ρ ≤ r`, the split polyradius is bounded above by `r`. -/
theorem splitRadius_le {r ρ : ℝ} (h : ρ ≤ r) : ∀ i : Option σ, splitRadius r ρ i ≤ r
  | none => le_rfl
  | some _ => h

/-- For `0 < ρ ≤ r`, the split polyradius is positive. -/
theorem splitRadius_pos {r ρ : ℝ} (hρ : 0 < ρ) (h : ρ ≤ r) (i : Option σ) :
    0 < splitRadius r ρ i :=
  hρ.trans_le (le_splitRadius h i)

/-- Separating a series restricted at radius `r` gives a univariate series restricted at `r`
with coefficients restricted at any radius `ρ ≤ r` in the remaining variables. -/
theorem isRestricted_of_map_subtype_eq_optionEquivLeft {ρ r : ℝ} [Fact (0 < ρ)] (hρr : ρ ≤ r)
    {f : MvPowerSeries (Option σ) R} (hf : IsRestricted (fun _ ↦ r) f)
    {F : PowerSeries (IsRestricted.subring (R := R) (fun _ : σ ↦ ρ))}
    (hF : PowerSeries.map (IsRestricted.subring (R := R) (fun _ : σ ↦ ρ)).subtype F =
      optionEquivLeft σ R f) :
    PowerSeries.IsRestricted r F := by
  -- Pass through the split polyradius to use the restricted-series comparison.
  let c : Option σ → ℝ := splitRadius r ρ
  let _ : ∀ i, Fact (0 < c i) := fun i ↦ ⟨splitRadius_pos Fact.out hρr i⟩
  let fc : IsRestricted.subring (R := R) c :=
    ⟨f, TauCeti.MvPowerSeries.isRestricted_of_le hf (fun i ↦ (Fact.out : 0 < c i).le)
      (splitRadius_le hρr)⟩
  have h : (restrictedOptionEquiv fc : PowerSeries _) = F := PowerSeries.map_injective _
    Subtype.val_injective ((map_subtype_restrictedOptionEquiv fc).trans hF.symm)
  exact h ▸ (restrictedOptionEquiv fc).2

/-- The comparison sends the separated variable to the univariate variable. -/
@[simp]
theorem coe_restrictedOptionEquiv_X_none :
    (restrictedOptionEquiv (⟨X none, isRestricted_X c none⟩ : Flat) : PowerSeries Inner) =
      PowerSeries.X := by
  refine PowerSeries.map_injective (Inner).subtype Subtype.val_injective ?_
  rw [map_subtype_restrictedOptionEquiv]
  simp

/-- The comparison sends each remaining variable to the corresponding constant univariate
series. -/
@[simp]
theorem coe_restrictedOptionEquiv_X_some (i : σ) :
    (restrictedOptionEquiv (⟨X (some i), isRestricted_X c (some i)⟩ : Flat) :
      PowerSeries Inner) = PowerSeries.C ⟨X i, isRestricted_X _ i⟩ := by
  refine PowerSeries.map_injective (Inner).subtype Subtype.val_injective ?_
  rw [map_subtype_restrictedOptionEquiv]
  simp

/-- The comparison preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedOptionEquiv (f : Flat) : ‖restrictedOptionEquiv f‖ = ‖f‖ := by
  have hpos (n : ℕ) : 0 < c none ^ n := pow_pos Fact.out n
  apply le_antisymm
  · rw [TauCeti.PowerSeries.norm_le_iff (norm_nonneg _)]
    intro n
    rw [← le_div_iff₀ (hpos n), MvPowerSeries.norm_le_iff
      (div_nonneg (norm_nonneg _) (hpos n).le)]
    intro t
    rw [le_div_iff₀ (hpos n), coeff_restrictedOptionEquiv,
      norm_coeff_coeff_optionEquivLeft_mul_prod_mul_pow]
    exact MvPowerSeries.norm_coeff_mul_prod_le f _
  · rw [MvPowerSeries.norm_le_iff (norm_nonneg _)]
    intro t
    rw [← Finsupp.optionElim_some t, ← norm_coeff_coeff_optionEquivLeft_mul_prod_mul_pow,
      ← coeff_restrictedOptionEquiv]
    exact (mul_le_mul_of_nonneg_right (MvPowerSeries.norm_coeff_mul_prod_le _ _) (hpos _).le).trans
      (TauCeti.PowerSeries.norm_coeff_mul_pow_le (restrictedOptionEquiv f) _)

/-- The comparison is an isometry for the Gauss norms. -/
theorem isometry_restrictedOptionEquiv :
    Isometry (restrictedOptionEquiv (σ := σ) (R := R) (c := c)) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr norm_restrictedOptionEquiv

section Split

variable {ι : Type*} (e : ι ≃ Option σ)

/-- Separate a specified variable after reindexing. The variable `e.symm none` becomes the
univariate variable; the others, labelled by `σ`, become variables in the coefficient algebra.
The source polyradii are `c ∘ e`, so this comparison applies at arbitrary positive radii. -/
noncomputable def restrictedSplitEquiv :
    IsRestricted.subring (R := R) (c ∘ e) ≃ₐ[R] Iter :=
  (IsRestricted.renameAlgEquiv e c).trans restrictedOptionEquiv

/-- Splitting after reindexing agrees with renaming followed by the native option comparison. -/
theorem restrictedSplitEquiv_apply (f : IsRestricted.subring (R := R) (c ∘ e)) :
    restrictedSplitEquiv e f = restrictedOptionEquiv (IsRestricted.renameAlgEquiv e c f) :=
  (rfl)

/-- On ambient formal series, splitting is Mathlib's option comparison after renaming. -/
@[simp]
theorem map_subtype_restrictedSplitEquiv (f : IsRestricted.subring (R := R) (c ∘ e)) :
    PowerSeries.map (Inner).subtype (restrictedSplitEquiv e f : PowerSeries Inner) =
      optionEquivLeft σ R (renameEquiv R e (f : MvPowerSeries ι R)) := by
  rw [restrictedSplitEquiv_apply, map_subtype_restrictedOptionEquiv,
    IsRestricted.coe_renameAlgEquiv]

/-- The coefficients of a split series are the original coefficients with their exponents
transported back along the chosen variable labelling. -/
@[simp]
theorem coeff_coeff_restrictedSplitEquiv (f : IsRestricted.subring (R := R) (c ∘ e))
    (n : ℕ) (t : σ →₀ ℕ) :
    coeff t (PowerSeries.coeff (R := Inner) n (restrictedSplitEquiv e f : PowerSeries Inner) :
      MvPowerSeries σ R) =
      coeff ((t.optionElim n).equivMapDomain e.symm) (f : MvPowerSeries ι R) := by
  have h := congrArg (fun F ↦ coeff t (PowerSeries.coeff n F))
    (map_subtype_restrictedSplitEquiv e f)
  simp only [PowerSeries.coeff_map, Subring.subtype_apply, coeff_coeff_optionEquivLeft] at h
  rw [h]
  have hc := coeff_embDomain_rename e.toEmbedding (f : MvPowerSeries ι R)
    ((t.optionElim n).equivMapDomain e.symm)
  simpa [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding,
    ← Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.equivMapDomain_trans] using hc

/-- Flattening a split series reads its coefficient at the exponent of the chosen variable
and at the exponents of the remaining variables. -/
@[simp]
theorem coeff_restrictedSplitEquiv_symm (F : Iter) (t : ι →₀ ℕ) :
    coeff t ((restrictedSplitEquiv e).symm F : MvPowerSeries ι R) =
      coeff (t.equivMapDomain e).some
        (PowerSeries.coeff (R := Inner) (t (e.symm none)) (F : PowerSeries Inner) :
          MvPowerSeries σ R) := by
  have h := coeff_coeff_restrictedSplitEquiv e ((restrictedSplitEquiv e).symm F)
    (t (e.symm none)) (t.equivMapDomain e).some
  have ht : (t.equivMapDomain e).some.optionElim (t (e.symm none)) =
      t.equivMapDomain e := Finsupp.optionElim_some _
  simpa only [AlgEquiv.apply_symm_apply, ht, ← Finsupp.equivMapDomain_trans,
    Equiv.self_trans_symm, Finsupp.equivMapDomain_refl] using h.symm

/-- Vanishing in all univariate degrees at least `s` means that the original series has degree
less than `s` in the chosen variable `e.symm none`. -/
theorem forall_coeff_restrictedSplitEquiv_eq_zero_iff
    (f : IsRestricted.subring (R := R) (c ∘ e)) (s : ℕ) :
    (∀ n, s ≤ n → PowerSeries.coeff n (restrictedSplitEquiv e f : PowerSeries Inner) = 0) ↔
      ∀ t : ι →₀ ℕ, s ≤ t (e.symm none) → coeff t (f : MvPowerSeries ι R) = 0 := by
  rw [restrictedSplitEquiv_apply, forall_coeff_restrictedOptionEquiv_eq_zero_iff]
  have hc (t : ι →₀ ℕ) :
      coeff (t.equivMapDomain e)
        (IsRestricted.renameAlgEquiv e c f : MvPowerSeries (Option σ) R) =
      coeff t (f : MvPowerSeries ι R) := by
    simpa [IsRestricted.coe_renameAlgEquiv, Finsupp.embDomain_eq_mapDomain,
      Equiv.coe_toEmbedding, Finsupp.equivMapDomain_eq_mapDomain] using
      coeff_embDomain_rename e.toEmbedding (f : MvPowerSeries ι R) t
  constructor
  · intro h t ht
    rw [← hc]
    exact h _ ht
  · intro h t ht
    obtain ⟨u, rfl⟩ := (Finsupp.equivCongrLeft e).surjective t
    rw [Finsupp.equivCongrLeft_apply, hc]
    exact h u ht

/-- Splitting sends the selected variable to the univariate variable. -/
@[simp]
theorem coe_restrictedSplitEquiv_X_none :
    (restrictedSplitEquiv e (⟨X (e.symm none), isRestricted_X _ _⟩ :
      IsRestricted.subring (R := R) (c ∘ e)) : PowerSeries Inner) = PowerSeries.X := by
  apply PowerSeries.map_injective (Inner).subtype Subtype.val_injective
  simp [map_subtype_restrictedSplitEquiv, renameEquiv]

/-- Splitting sends the other variables to constants with values in the coefficient algebra. -/
@[simp]
theorem coe_restrictedSplitEquiv_X_some (i : σ) :
    (restrictedSplitEquiv e (⟨X (e.symm (some i)), isRestricted_X _ _⟩ :
      IsRestricted.subring (R := R) (c ∘ e)) : PowerSeries Inner) =
      PowerSeries.C ⟨X i, isRestricted_X _ _⟩ := by
  apply PowerSeries.map_injective (Inner).subtype Subtype.val_injective
  simp [map_subtype_restrictedSplitEquiv, renameEquiv]

/-- Splitting in any specified variable preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedSplitEquiv (f : IsRestricted.subring (R := R) (c ∘ e)) :
    ‖restrictedSplitEquiv e f‖ = ‖f‖ := by
  rw [restrictedSplitEquiv_apply, norm_restrictedOptionEquiv, IsRestricted.norm_renameAlgEquiv]

/-- The comparison for a specified variable is an isometry. -/
theorem isometry_restrictedSplitEquiv :
    Isometry (restrictedSplitEquiv (R := R) (c := c) e) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedSplitEquiv e)

end Split

end MvPowerSeries
