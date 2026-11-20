/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Sobolev.Wkp.Kernel
public import TauCeti.Analysis.Sobolev.Wkp.Seminorm

/-!
# Polynomial classes in `W^{k,p}(Ω)` and the quotient by them

For an open set `Ω ⊆ EuclideanSpace ℝ ι`, the **polynomial classes of degree at most `m`**
`TauCeti.Wkp.polynomialClasses m k` form the subspace of `W^{k,p}(Ω)` whose values agree almost
everywhere on `Ω` with a polynomial function in `TauCeti.polynomialsDegLE ι m`. They are the
functions that polynomial approximation estimates of Bramble–Hilbert type subtract. Every seminorm
`|·|_{j,p}` with `m < j ≤ k` vanishes on them
(`TauCeti.Wkp.seminorm_eq_zero_of_mem_polynomialClasses`) and is unchanged by subtracting them
(`TauCeti.Wkp.seminorm_sub_of_mem_polynomialClasses`). On a preconnected domain the polynomial
classes of degree at most `m` are precisely the kernel of the top weak derivative on
`W^{m+1,p}(Ω)` (`TauCeti.Wkp.ker_iteratedGradientL`).

On a bounded domain every polynomial function lies in `W^{k,p}(Ω)`, which gives the continuous
linear map `TauCeti.Wkp.ofPolynomialL : polynomialsDegLE ι m →L[ℝ] W^{k,p}(Ω)` sending a
polynomial to its Sobolev class. Its range is the subspace of polynomial classes, so that subspace
is finite-dimensional and closed. For nonempty `Ω` the map is injective, so the subspace has
dimension `(m + n).choose n` with `n = Fintype.card ι`. Boundedness cannot be dropped for the
map: the constant `1` is not in `Lᵖ(ℝⁿ)` for `p < ∞`. Nonemptiness cannot be dropped for
injectivity, since `W^{k,p}(∅)` is the zero space.

The quotient `W^{m+1,p}(Ω) ⧸ polynomialClasses m (m + 1)` carries Mathlib's quotient norm
`‖[u]‖ = inf_q ‖u - q‖` and is complete. On a bounded domain the polynomial classes are
closed (`TauCeti.Wkp.isClosed_polynomialClasses`), so Mathlib's
`Submodule.Quotient.normedAddCommGroup` makes the quotient a Banach space. The top seminorm
`|·|_{m+1,p}` descends to the quotient as `TauCeti.Wkp.quotientSeminorm m`, is bounded there by
the quotient norm, and on a preconnected domain it vanishes only at zero
(`TauCeti.Wkp.quotientSeminorm_eq_zero_iff`). The Deny–Lions lemma compares these two quantities
on the quotient.

## Main declarations

* `TauCeti.Wkp.polynomialClasses`: the subspace of polynomial classes of degree at most `m`.
* `TauCeti.Wkp.ker_iteratedGradientL`: on a preconnected domain, the kernel of the top weak
  derivative on `W^{m+1,p}(Ω)` is `polynomialClasses m (m + 1)`.
* `TauCeti.Wkp.ofPolynomialL`: the Sobolev class of a polynomial on a bounded domain.
* `TauCeti.Wkp.seminorm_ofPolynomialL`, `TauCeti.Wkp.seminorm_sub_ofPolynomialL`: seminorms of
  order exceeding the degree vanish on, and are unchanged by subtracting, Sobolev classes of
  polynomials.
* `TauCeti.Wkp.range_ofPolynomialL`, `TauCeti.Wkp.ofPolynomialL_injective`,
  `TauCeti.Wkp.finrank_polynomialClasses`, `TauCeti.Wkp.isClosed_polynomialClasses`.
* `TauCeti.Wkp.quotientIteratedGradientL`, `TauCeti.Wkp.quotientSeminorm`: the top weak derivative
  and the top seminorm on the quotient by polynomial classes.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer (2008), §4.3 and §4.4.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, North-Holland (1978), §3.1.
* J. Deny, J.-L. Lions, *Les espaces du type de Beppo Levi*, Ann. Inst. Fourier 5 (1954),
  305–370.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The subspace of polynomial classes -/

/-- The **polynomial classes of degree at most `m`** in `W^{k,p}(Ω)`: the Sobolev functions whose
value agrees almost everywhere on `Ω` with a polynomial function of total degree at most `m`. -/
def polynomialClasses (m k : ℕ) : Submodule ℝ (Wkp mu Omega p k) where
  carrier := {u | ∃ q ∈ polynomialsDegLE ι m,
    (value k u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q}
  add_mem' := by
    rintro u v ⟨q, hq, hu⟩ ⟨r, hr, hv⟩
    refine ⟨q + r, add_mem hq hr, ?_⟩
    rw [value_add]
    exact (Lp.coeFn_add _ _).trans (hu.add hv)
  zero_mem' := ⟨0, zero_mem _, by
    rw [← valueL_apply, map_zero]
    exact Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c u ⟨q, hq, hu⟩
    refine ⟨c • q, Submodule.smul_mem _ c hq, ?_⟩
    rw [value_smul]
    exact (Lp.coeFn_smul _ _).trans (hu.const_smul c)

/-- A Sobolev function is a polynomial class of degree at most `m` exactly when its value agrees
almost everywhere on `Ω` with a polynomial function of total degree at most `m`. -/
theorem mem_polynomialClasses_iff {m k : ℕ} {u : Wkp mu Omega p k} :
    u ∈ polynomialClasses m k ↔ ∃ q ∈ polynomialsDegLE ι m,
      (value k u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q :=
  Iff.rfl

/-- Polynomial classes of degree at most `m` are polynomial classes of every larger degree. -/
theorem polynomialClasses_mono {m m' : ℕ} (h : m ≤ m') (k : ℕ) :
    polynomialClasses (mu := mu) (Omega := Omega) (p := p) m k ≤ polynomialClasses m' k :=
  fun _ ⟨q, hq, hu⟩ ↦ ⟨q, polynomialsDegLE_mono ι h hq, hu⟩

/-- Order truncation maps polynomial classes to polynomial classes of the same degree. -/
theorem toOrderL_mem_polynomialClasses {m j k : ℕ} (h : j ≤ k) {u : Wkp mu Omega p k}
    (hu : u ∈ polynomialClasses m k) : toOrderL h u ∈ polynomialClasses m j := by
  obtain ⟨q, hq, hu⟩ := hu
  exact ⟨q, hq, by rwa [value_toOrderL]⟩

/-- Forgetting the top derivative maps polynomial classes to polynomial classes of the same
degree. -/
theorem lowerOrder_mem_polynomialClasses {m k : ℕ} {u : Wkp mu Omega p (k + 1)}
    (hu : u ∈ polynomialClasses m (k + 1)) : lowerOrder k u ∈ polynomialClasses m k := by
  obtain ⟨q, hq, hu⟩ := hu
  exact ⟨q, hq, by rwa [← value_succ]⟩

/-- A polynomial class of degree at most `m` in `W^{k+1,p}(Ω)`, with `m ≤ k`, has vanishing
`(k + 1)`-st weak derivative. -/
theorem iteratedGradient_eq_zero_of_mem_polynomialClasses {m k : ℕ} (hmk : m ≤ k)
    {u : Wkp mu Omega p (k + 1)} (hu : u ∈ polynomialClasses m (k + 1)) :
    iteratedGradient k u = 0 := by
  obtain ⟨q, hq, hu⟩ := hu
  exact iteratedGradient_eq_zero_of_ae_eq_mem_polynomialsDegLE hmk hq hu

/-- Every Sobolev seminorm of order exceeding `m` vanishes on the polynomial classes of degree at
most `m`. -/
theorem seminorm_eq_zero_of_mem_polynomialClasses {m j k : ℕ} (hmj : m < j) (hj : j ≤ k)
    {u : Wkp mu Omega p k} (hu : u ∈ polynomialClasses m k) : seminorm k j hj u = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := Nat.exists_eq_add_one_of_ne_zero (by omega)
  rw [seminorm_succ_apply, iteratedGradient_eq_zero_of_mem_polynomialClasses (by omega)
    (toOrderL_mem_polynomialClasses hj hu), norm_zero]

/-- Subtracting a polynomial class of degree at most `m` does not change any Sobolev seminorm of
order exceeding `m`. -/
theorem seminorm_sub_of_mem_polynomialClasses {m j k : ℕ} (hmj : m < j) (hj : j ≤ k)
    (u : Wkp mu Omega p k) {q : Wkp mu Omega p k} (hq : q ∈ polynomialClasses m k) :
    seminorm k j hj (u - q) = seminorm k j hj u := by
  have hq0 := seminorm_eq_zero_of_mem_polynomialClasses hmj hj hq
  refine le_antisymm ((map_sub_le_add _ u q).trans_eq (by rw [hq0, add_zero])) ?_
  calc seminorm k j hj u = seminorm k j hj (u - q + q) := by rw [sub_add_cancel]
    _ ≤ seminorm k j hj (u - q) + seminorm k j hj q := map_add_le_add _ _ _
    _ = seminorm k j hj (u - q) := by rw [hq0, add_zero]

/-- The polynomial classes of degree at most `k` lie in the kernel of the top weak derivative on
`W^{k+1,p}(Ω)`. -/
theorem polynomialClasses_le_ker_iteratedGradientL (k : ℕ) :
    polynomialClasses k (k + 1) ≤
      (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) k).ker :=
  fun _ hu ↦ by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, iteratedGradientL_apply]
    exact iteratedGradient_eq_zero_of_mem_polynomialClasses le_rfl hu

/-- **Kernel of the top weak derivative.** On a preconnected domain, the kernel of the top weak
derivative `iteratedGradientL m` on `W^{m+1,p}(Ω)` is exactly the subspace of polynomial classes
of degree at most `m`. -/
theorem ker_iteratedGradientL (hOmega : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (m : ℕ) :
    (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).ker =
      polynomialClasses m (m + 1) := by
  ext u
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, iteratedGradientL_apply,
    iteratedGradient_eq_zero_iff hOmega, mem_polynomialClasses_iff]

/-! ### Sobolev classes of polynomials on bounded domains -/

section Bounded

variable (hOmega : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
include hOmega

/-- On a bounded domain, every polynomial function represents an element of `W^{k,p}(Ω)`. -/
private theorem exists_value_ae_eq_of_mem_polynomialsDegLE (k : ℕ) {m : ℕ}
    {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m) :
    ∃ u : Wkp mu Omega p k,
      (value k u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q :=
  exists_value_ae_eq_of_contDiffOn_of_isCompact k isOpen_univ
    (contDiff_of_mem_polynomialsDegLE hq).contDiffOn hOmega.isCompact_closure subset_closure
    (Set.subset_univ _)

/-- The value of the chosen representative of a polynomial agrees with it almost everywhere. -/
private theorem value_choose_ae (k : ℕ) {m : ℕ} (q : polynomialsDegLE ι m) :
    (value k (exists_value_ae_eq_of_mem_polynomialsDegLE (mu := mu) (p := p) hOmega k q.2).choose :
      EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q :=
  (exists_value_ae_eq_of_mem_polynomialsDegLE hOmega k q.2).choose_spec

/-- On a bounded domain, the **Sobolev class of a polynomial**: the continuous linear map
`polynomialsDegLE ι m →L[ℝ] W^{k,p}(Ω)` sending a polynomial function to the element of
`W^{k,p}(Ω)` it represents (`TauCeti.Wkp.value_ofPolynomialL_ae`). -/
def ofPolynomialL (m k : ℕ) : polynomialsDegLE ι m →L[ℝ] Wkp mu Omega p k :=
  LinearMap.toContinuousLinearMap
    { toFun q := (exists_value_ae_eq_of_mem_polynomialsDegLE hOmega k q.2).choose
      map_add' q r := ext k <| Lp.ext <| (value_choose_ae hOmega k (q + r)).trans <| by
        rw [value_add]
        exact ((value_choose_ae hOmega k q).add (value_choose_ae hOmega k r)).symm.trans
          (Lp.coeFn_add _ _).symm
      map_smul' c q := ext k <| Lp.ext <| (value_choose_ae hOmega k (c • q)).trans <| by
        rw [RingHom.id_apply, value_smul]
        exact ((value_choose_ae hOmega k q).const_smul c).symm.trans (Lp.coeFn_smul _ _).symm }

/-- The value of the Sobolev class of a polynomial agrees almost everywhere on `Ω` with the
polynomial. -/
theorem value_ofPolynomialL_ae (m k : ℕ) (q : polynomialsDegLE ι m) :
    (value k (ofPolynomialL (mu := mu) (p := p) hOmega m k q) : EuclideanSpace ℝ ι → ℝ)
      =ᵐ[mu.restrict Omega] q :=
  value_choose_ae hOmega k q

/-- The Sobolev class of a polynomial is the unique element of `W^{k,p}(Ω)` whose value agrees with
it almost everywhere on `Ω`. -/
theorem ofPolynomialL_eq_iff {m k : ℕ} {q : polynomialsDegLE ι m} {u : Wkp mu Omega p k} :
    ofPolynomialL hOmega m k q = u ↔
      (value k u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q := by
  refine ⟨fun h ↦ h ▸ value_ofPolynomialL_ae hOmega m k q, fun h ↦ ext k (Lp.ext ?_)⟩
  exact (value_ofPolynomialL_ae hOmega m k q).trans h.symm

/-- Truncating the Sobolev class of a polynomial gives its Sobolev class of lower order. -/
@[simp]
theorem toOrderL_ofPolynomialL {m j k : ℕ} (h : j ≤ k) (q : polynomialsDegLE ι m) :
    toOrderL h (ofPolynomialL (mu := mu) (p := p) hOmega m k q) = ofPolynomialL hOmega m j q := by
  rw [eq_comm, ofPolynomialL_eq_iff, value_toOrderL]
  exact value_ofPolynomialL_ae hOmega m k q

/-- Forgetting the top derivative of the Sobolev class of a polynomial gives its Sobolev class of
lower order. -/
theorem lowerOrder_ofPolynomialL {m k : ℕ} (q : polynomialsDegLE ι m) :
    lowerOrder k (ofPolynomialL (mu := mu) (p := p) hOmega m (k + 1) q) =
      ofPolynomialL hOmega m k q := by
  rw [eq_comm, ofPolynomialL_eq_iff, ← value_succ]
  exact value_ofPolynomialL_ae hOmega m (k + 1) q

/-- The Sobolev class of a polynomial of degree at most `m` is a polynomial class of degree at
most `m`. -/
@[simp]
theorem ofPolynomialL_mem_polynomialClasses {m k : ℕ} (q : polynomialsDegLE ι m) :
    ofPolynomialL (mu := mu) (p := p) hOmega m k q ∈ polynomialClasses m k :=
  ⟨q, q.2, value_ofPolynomialL_ae hOmega m k q⟩

/-- Every Sobolev seminorm of order exceeding `m` vanishes on the Sobolev class of a polynomial of
degree at most `m`. -/
theorem seminorm_ofPolynomialL {m j k : ℕ} (hmj : m < j) (hj : j ≤ k) (q : polynomialsDegLE ι m) :
    seminorm k j hj (ofPolynomialL (mu := mu) (p := p) hOmega m k q) = 0 :=
  seminorm_eq_zero_of_mem_polynomialClasses hmj hj (ofPolynomialL_mem_polynomialClasses hOmega q)

/-- Subtracting the Sobolev class of a polynomial of degree at most `m` does not change any Sobolev
seminorm of order exceeding `m`. -/
theorem seminorm_sub_ofPolynomialL {m j k : ℕ} (hmj : m < j) (hj : j ≤ k)
    (u : Wkp mu Omega p k) (q : polynomialsDegLE ι m) :
    seminorm k j hj (u - ofPolynomialL hOmega m k q) = seminorm k j hj u :=
  seminorm_sub_of_mem_polynomialClasses hmj hj u (ofPolynomialL_mem_polynomialClasses hOmega q)

/-- The Sobolev classes of polynomials of degree at most `m` are exactly the polynomial classes of
degree at most `m`. -/
theorem range_ofPolynomialL (m k : ℕ) :
    (ofPolynomialL (mu := mu) (p := p) hOmega m k).range = polynomialClasses m k := by
  ext u
  refine ⟨?_, fun ⟨q, hq, hu⟩ ↦ ⟨⟨q, hq⟩, (ofPolynomialL_eq_iff hOmega).2 hu⟩⟩
  rintro ⟨q, rfl⟩
  exact ofPolynomialL_mem_polynomialClasses hOmega q

/-- On a nonempty bounded domain, distinct polynomials have distinct Sobolev classes. -/
theorem ofPolynomialL_injective (hne : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) (m k : ℕ) :
    Function.Injective (ofPolynomialL (mu := mu) (p := p) hOmega m k) := by
  intro q r h
  have hqr : (q : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] r :=
    (value_ofPolynomialL_ae hOmega m k q).symm.trans
      (h ▸ value_ofPolynomialL_ae (mu := mu) (p := p) hOmega m k r)
  exact Subtype.ext (eq_of_mem_polynomialsDegLE_of_ae_eq_isOpen q.2 r.2 Omega.isOpen hne hqr)

/-- On a bounded domain, the polynomial classes of degree at most `m` form a finite-dimensional
subspace of `W^{k,p}(Ω)`. -/
theorem finiteDimensional_polynomialClasses (m k : ℕ) :
    FiniteDimensional ℝ (polynomialClasses (mu := mu) (Omega := Omega) (p := p) m k) := by
  rw [← range_ofPolynomialL hOmega]
  exact LinearMap.finiteDimensional_range _

/-- On a nonempty bounded domain, the polynomial classes of degree at most `m` in `n = card ι`
variables form a subspace of `W^{k,p}(Ω)` of dimension `(m + n).choose n`. -/
theorem finrank_polynomialClasses (hne : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (m k : ℕ) :
    Module.finrank ℝ (polynomialClasses (mu := mu) (Omega := Omega) (p := p) m k) =
      (m + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← range_ofPolynomialL hOmega, LinearMap.finrank_range_of_inj
    (ofPolynomialL_injective hOmega hne m k), finrank_polynomialsDegLE]

/-- On a bounded domain, the polynomial classes of degree at most `m` form a closed subspace of
`W^{k,p}(Ω)`. -/
theorem isClosed_polynomialClasses (m k : ℕ) :
    IsClosed
      ((polynomialClasses m k : Submodule ℝ (Wkp mu Omega p k)) : Set (Wkp mu Omega p k)) :=
  have := finiteDimensional_polynomialClasses (mu := mu) (p := p) hOmega m k
  Submodule.isClosed_of_finiteDimensional _

end Bounded

/-! ### The top seminorm on the quotient by polynomial classes -/

/-- The top weak derivative `iteratedGradientL m`, which vanishes on the polynomial classes of
degree at most `m`, descended to the quotient `W^{m+1,p}(Ω) ⧸ polynomialClasses m (m + 1)`. -/
def quotientIteratedGradientL (m : ℕ) :
    Wkp mu Omega p (m + 1) ⧸ polynomialClasses m (m + 1) →L[ℝ]
      Lp (IteratedGradient (EuclideanSpace ℝ ι) m) p (mu.restrict Omega) :=
  (polynomialClasses m (m + 1)).liftQL (iteratedGradientL m)
    (polynomialClasses_le_ker_iteratedGradientL m)

/-- The descended top weak derivative of a class is the top weak derivative of any
representative. -/
theorem quotientIteratedGradientL_mk (m : ℕ) (u : Wkp mu Omega p (m + 1)) :
    quotientIteratedGradientL m (Submodule.Quotient.mk u) = iteratedGradient m u := by
  rw [quotientIteratedGradientL, Submodule.liftQL_apply, Submodule.liftQ_apply,
    ContinuousLinearMap.coe_coe, iteratedGradientL_apply]

/-- The **top seminorm on the quotient by polynomials**: the seminorm `|·|_{m+1,p}` on
`W^{m+1,p}(Ω)`, which is invariant under adding polynomial classes of degree at most `m`, descended
to `W^{m+1,p}(Ω) ⧸ polynomialClasses m (m + 1)`. -/
def quotientSeminorm (m : ℕ) :
    Seminorm ℝ (Wkp mu Omega p (m + 1) ⧸ polynomialClasses m (m + 1)) :=
  (normSeminorm ℝ (Lp (IteratedGradient (EuclideanSpace ℝ ι) m) p (mu.restrict Omega))).comp
    (quotientIteratedGradientL m).toLinearMap

/-- The top seminorm on the quotient evaluates on a class to the top seminorm of any
representative. -/
theorem quotientSeminorm_mk (m : ℕ) (u : Wkp mu Omega p (m + 1)) :
    quotientSeminorm m (Submodule.Quotient.mk u) = seminorm (m + 1) (m + 1) le_rfl u := by
  rw [quotientSeminorm, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    quotientIteratedGradientL_mk, seminorm_succ_self_apply]

/-- The top seminorm on the quotient is continuous for the quotient norm. -/
theorem continuous_quotientSeminorm (m : ℕ) :
    Continuous (quotientSeminorm (mu := mu) (Omega := Omega) (p := p) m) :=
  continuous_norm.comp (quotientIteratedGradientL (mu := mu) (Omega := Omega) (p := p) m).continuous

/-- The top seminorm on the quotient is bounded by the quotient norm
`‖[u]‖ = inf_q ‖u - q‖`. -/
theorem quotientSeminorm_le_norm {m : ℕ}
    (x : Wkp mu Omega p (m + 1) ⧸ polynomialClasses m (m + 1)) :
    quotientSeminorm m x ≤ ‖x‖ := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨u, rfl, hu⟩ := Submodule.Quotient.norm_mk_lt x hε
  rw [quotientSeminorm_mk]
  exact (seminorm_le_norm le_rfl u).trans_lt hu

/-- On a preconnected domain, the top seminorm on the quotient by polynomial classes vanishes only
at zero, so it is a norm on the quotient. -/
theorem quotientSeminorm_eq_zero_iff (hOmega : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    {m : ℕ} (x : Wkp mu Omega p (m + 1) ⧸ polynomialClasses m (m + 1)) :
    quotientSeminorm m x = 0 ↔ x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    rw [quotientSeminorm_mk, seminorm_succ_self_apply, norm_eq_zero,
      Submodule.Quotient.mk_eq_zero, ← ker_iteratedGradientL hOmega, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, iteratedGradientL_apply]

end TauCeti.Wkp
