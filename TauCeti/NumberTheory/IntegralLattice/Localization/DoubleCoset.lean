/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.ClassNumber
public import TauCeti.NumberTheory.IntegralLattice.Localization.Stabilizer
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.DoubleCoset.Basic

/-!
# Finite adelic translates of a lattice and the double-coset description of its genus

Let `L` be a nondegenerate integral lattice in the rational quadratic space `V`, and write
`O(V)(𝔸_f)` for the restricted product of the local orthogonal groups `O(V_p)` relative to the
local stabilizers `K_p(L) = {g ∈ O(V_p) : g L_p = L_p}`. An element `g = (g_p)` of `O(V)(𝔸_f)`
lies in `K_p(L)` at almost every prime, so the local lattices `g_p L_p ⊆ V_p` agree with `L_p` at
almost every prime, and by the local–global correspondence for lattices
(`Submodule.existsUnique_isLattice_padicLocalization_eq`) they are the localizations of exactly one
lattice

```text
g • L = {v ∈ V | 1 ⊗ v ∈ g_p L_p for every prime p}.
```

Since every `g_p` is an isometry, `g • L` is again integral for the rational form of `L`
(`TauCeti.IntegralLattice.adelicTranslate`), and it lies in the genus of `L`. Conversely, every
lattice on the quadratic space of `L` in the genus of `L` is such a translate: an integral local
isometry `L_p ≅ M_p` extends to an element of `O(V_p)` carrying `L_p` onto `M_p`, and it may be
taken to be the identity at the almost all primes where `M_p = L_p`.

Two translates `g • L` and `h • L` coincide exactly when `g⁻¹ h` lies in the everywhere-integral
subgroup `K_f(L) = ∏_p K_p(L)`, and a rational isometry `γ` carries `g • L` to `γ g • L`. Hence the
isometry class of `g • L` depends only on the double coset of `g`, and the resulting map

```text
O(V)(ℚ) \ O(V)(𝔸_f) / K_f(L) → classes in the genus of L
```

is injective (`TauCeti.IntegralLattice.doubleCosetClass_injective`), with image the classes of the
lattices in the genus of `L` which lie on the quadratic space `(V, B)` of `L` itself
(`TauCeti.IntegralLattice.mem_range_doubleCosetClass_iff`). Every class of the genus has such a
representative as soon as the rational forms of the lattices in the genus are isometric to that of
`L`, which is what makes this map a bijection onto the genus; that comparison of rational forms is
not proved here.

## Main definitions

* `TauCeti.IntegralLattice.adelicTranslate`: the translate `g • L` of `L` by an element `g` of
  the finite adelic orthogonal group.
* `TauCeti.IntegralLattice.doubleCosetClass`: the isometry class of `g • L`, as a function of the
  double coset of `g`.

## Main results

* `TauCeti.IntegralLattice.padicLocalization_adelicTranslate_carrier`: `(g • L)_p = g_p L_p`.
* `TauCeti.IntegralLattice.adelicTranslate_eq_adelicTranslate_iff`: `g • L = h • L` exactly when
  `g⁻¹ h ∈ K_f(L)`.
* `TauCeti.IntegralLattice.adelicTranslate_finiteAdelicOrthogonalDiagonal_mul_carrier`: a rational
  isometry `γ` carries `g • L` onto `γ g • L`.
* `TauCeti.IntegralLattice.sameGenus_adelicTranslate`: `g • L` lies in the genus of `L`.
* `TauCeti.IntegralLattice.exists_adelicTranslate_eq`: every lattice on the quadratic space of `L`
  in the genus of `L` is a translate of `L`.
* `TauCeti.IntegralLattice.doubleCosetClass_injective`,
  `TauCeti.IntegralLattice.mem_range_doubleCosetClass_iff`: the double cosets are in bijection with
  the classes of the genus of `L` represented on the quadratic space of `L`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §81E and §§101–102, for the adelic
  action on lattices and the description of the classes in a genus by adelic double cosets.
* M. Kneser, *Quadratische Formen* (2002), §§21–22.
-/

public section

open Module Filter TauCeti.QuadraticMap
open scoped TensorProduct

namespace TauCeti

namespace IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V) [L.IsNondegenerate]

section AdelicTranslate

variable (g : L.orthogonalCompactOpens.finiteAdelicOrthogonal)

/-- The carrier of `adelicTranslate`: the vectors `v` with `1 ⊗ v ∈ g_p L_p` at every prime. -/
private def adelicTranslateCarrier : Submodule ℤ V where
  carrier := {v | ∀ p : Nat.Primes, (1 : ℚ_[p]) ⊗ₜ[ℚ] v ∈ L.localTranslate p (g p)}
  add_mem' ha hb p := by simpa only [TensorProduct.tmul_add] using add_mem (ha p) (hb p)
  zero_mem' p := by simp
  smul_mem' n v hv p := by simpa only [TensorProduct.tmul_smul] using zsmul_mem (hv p) n

/-- The local lattices `g_p L_p` are the localizations of the carrier of `adelicTranslate`. -/
private theorem isLattice_and_padicLocalization_adelicTranslateCarrier :
    (adelicTranslateCarrier L g).IsLattice ℚ ∧
      ∀ p : Nat.Primes, (adelicTranslateCarrier L g).padicLocalization p =
        L.localTranslate p (g p) := by
  -- At almost every prime `g_p ∈ K_p(L)`, so that `g_p L_p = L_p`.
  have hX : ∀ᶠ p : Nat.Primes in cofinite,
      L.localTranslate p (g p) = L.carrier.padicLocalization p :=
    g.2.mono fun p hp ↦ (L.mem_localStabilizer_iff_localTranslate_eq p).mp
      (L.orthogonalCompactOpens_orthogonal p ▸ hp)
  obtain ⟨M, ⟨hM, hMX⟩, -⟩ := Submodule.existsUnique_isLattice_padicLocalization_eq _ hX
  obtain rfl : M = adelicTranslateCarrier L g := Submodule.ext fun v ↦ by
    rw [Submodule.mem_iff_forall_one_tmul_mem_padicLocalization (N := M) v]
    exact forall_congr' fun p ↦ by rw [hMX p]
  exact ⟨hM, hMX⟩

/-- The rational form takes integral values on the carrier of `adelicTranslate`, since `g_p` is
an isometry of `V_p` and the form is `p`-adically integral on `L_p`. -/
private theorem norm_form_le_one_of_mem_adelicTranslateCarrier {v w : V}
    (hv : v ∈ adelicTranslateCarrier L g) (hw : w ∈ adelicTranslateCarrier L g) (p : Nat.Primes) :
    ‖(L.form v w : ℚ_[p])‖ ≤ 1 := by
  have hv' := mem_localTranslate_iff.mp (hv p)
  have hw' := mem_localTranslate_iff.mp (hw p)
  rw [← L.range_localizationToCompletion] at hv' hw'
  obtain ⟨a, ha⟩ := hv'
  obtain ⟨b, hb⟩ := hw'
  have hg : (g p : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V) ∈
      (L.completedRationalForm p).isometryGroup :=
    L.orthogonalGroup_norm_baseChange p ▸ (g p).2
  have h := LinearMap.BilinForm.mem_isometryGroup_iff.mp hg (L.localizationToCompletion p a)
    (L.localizationToCompletion p b)
  have hva : (g p : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V) (L.localizationToCompletion p a) =
      1 ⊗ₜ v := by rw [ha, LinearEquiv.apply_symm_apply]
  have hwb : (g p : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V) (L.localizationToCompletion p b) =
      1 ⊗ₜ w := by rw [hb, LinearEquiv.apply_symm_apply]
  rw [hva, hwb, completedRationalForm_tmul, completedRationalForm_localizationToCompletion,
    one_mul, one_mul] at h
  rw [h, PadicInt.algebraMap_apply]
  exact PadicInt.norm_le_one _

/-- **The translate `g • L` of `L` by a finite adele** `g ∈ O(V)(𝔸_f)`: the lattice on the
quadratic space of `L` whose localization at every prime `p` is `g_p L_p`. It consists of the
vectors `v` with `1 ⊗ v ∈ g_p L_p` at every prime. -/
noncomputable def adelicTranslate : IntegralLattice V where
  carrier := adelicTranslateCarrier L g
  form := L.form
  isLattice := (isLattice_and_padicLocalization_adelicTranslateCarrier L g).1
  isSymm := L.isSymm
  le_dual v hv := (LinearMap.BilinForm.mem_dualSubmodule _).mpr fun w hw ↦
    Submodule.mem_one.mpr ⟨(L.form v w).num, by
      rw [algebraMap_int_eq, eq_intCast, ← Rat.den_eq_one_iff]
      exact Padic.forall_norm_rat_le_one_iff_den_eq_one.mp
        (norm_form_le_one_of_mem_adelicTranslateCarrier L g hv hw)⟩

/-- A translate of `L` carries the rational form of `L`. -/
@[simp]
theorem adelicTranslate_form : (L.adelicTranslate g).form = L.form :=
  (rfl)

/-- A translate of a nondegenerate lattice is nondegenerate, since it carries the same form. -/
instance instIsNondegenerateAdelicTranslate : (L.adelicTranslate g).IsNondegenerate :=
  ⟨by rw [adelicTranslate_form]; exact L.form_nondegenerate⟩

/-- A translate of `L` has the completed rational forms of `L`. -/
@[simp]
theorem adelicTranslate_completedRationalForm (p : ℕ) [Fact p.Prime] :
    (L.adelicTranslate g).completedRationalForm p = L.completedRationalForm p := by
  rw [completedRationalForm_def, completedRationalForm_def, adelicTranslate_form]

/-- A vector lies in `g • L` exactly when `1 ⊗ v ∈ g_p L_p` at every prime. -/
theorem mem_adelicTranslate_carrier_iff {v : V} :
    v ∈ (L.adelicTranslate g).carrier ↔
      ∀ p : Nat.Primes, (1 : ℚ_[p]) ⊗ₜ[ℚ] v ∈ L.localTranslate p (g p) :=
  Iff.rfl

/-- **The localizations of `g • L` are the lattices `g_p L_p`.** -/
theorem padicLocalization_adelicTranslate_carrier (p : Nat.Primes) :
    (L.adelicTranslate g).carrier.padicLocalization p = L.localTranslate p (g p) :=
  (isLattice_and_padicLocalization_adelicTranslateCarrier L g).2 p

/-- The translate of `L` by the identity is `L`. -/
@[simp]
theorem adelicTranslate_one : L.adelicTranslate 1 = L := by
  refine IntegralLattice.ext ((Submodule.eq_iff_forall_padicLocalization_eq _).mpr fun p ↦ ?_) rfl
  rw [padicLocalization_adelicTranslate_carrier, RestrictedProduct.one_apply]
  exact (L.mem_localStabilizer_iff_localTranslate_eq p).mp (one_mem _)

/-- **Two translates of `L` coincide exactly when the adeles differ by an element of
`K_f(L) = ∏_p K_p(L)`.** -/
theorem adelicTranslate_eq_adelicTranslate_iff
    {g h : L.orthogonalCompactOpens.finiteAdelicOrthogonal} :
    L.adelicTranslate g = L.adelicTranslate h ↔
      g⁻¹ * h ∈ integralSubgroup L.orthogonalCompactOpens.orthogonal := by
  rw [IntegralLattice.ext_iff,
    and_iff_left ((L.adelicTranslate_form g).trans (L.adelicTranslate_form h).symm),
    Submodule.eq_iff_forall_padicLocalization_eq, mem_integralSubgroup]
  refine forall_congr' fun p ↦ ?_
  rw [padicLocalization_adelicTranslate_carrier, padicLocalization_adelicTranslate_carrier,
    L.orthogonalCompactOpens_orthogonal, L.mem_localStabilizer_iff_localTranslate_eq,
    RestrictedProduct.mul_apply, RestrictedProduct.inv_apply]
  simp only [Submodule.ext_iff, mem_localTranslate_iff]
  -- `(g_p⁻¹ h_p)⁻¹ = h_p⁻¹ g_p`; the two conditions correspond under `x ↦ g_p x`.
  have key (x : ℚ_[p] ⊗[ℚ] V) :
      ((↑((g p)⁻¹ * h p) : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V)).symm x =
        (h p : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V).symm
          ((g p : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V) x) := by
    rw [LinearEquiv.symm_apply_eq, Subgroup.coe_mul, mul_apply_eq_comp, Subgroup.coe_inv,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  simp only [key]
  refine ⟨fun H x ↦ ?_, fun H x ↦ ?_⟩
  · simpa only [LinearEquiv.symm_apply_apply] using
      (H ((g p : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V) x)).symm
  · simpa only [LinearEquiv.apply_symm_apply] using
      (H ((g p : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V).symm x)).symm

/-- A translate of `L` is `L` exactly when the adele lies in `K_f(L)`. -/
theorem adelicTranslate_eq_self_iff :
    L.adelicTranslate g = L ↔ g ∈ integralSubgroup L.orthogonalCompactOpens.orthogonal := by
  have h := L.adelicTranslate_eq_adelicTranslate_iff (g := g) (h := 1)
  rwa [adelicTranslate_one, mul_one, inv_mem_iff] at h

/-- **A rational isometry `γ` carries `g • L` onto `γ g • L`.** -/
theorem adelicTranslate_finiteAdelicOrthogonalDiagonal_mul_carrier (γ : orthogonalGroup L.norm) :
    (L.adelicTranslate (L.orthogonalCompactOpens.finiteAdelicOrthogonalDiagonal γ * g)).carrier =
      (L.adelicTranslate g).carrier.map ((γ : V ≃ₗ[ℚ] V).restrictScalars ℤ).toLinearMap := by
  ext v
  rw [Submodule.mem_map_equiv, mem_adelicTranslate_carrier_iff, mem_adelicTranslate_carrier_iff]
  refine forall_congr' fun p ↦ ?_
  rw [RestrictedProduct.mul_apply, OrthogonalCompactOpens.finiteAdelicOrthogonalDiagonal_apply,
    mem_localTranslate_iff, mem_localTranslate_iff, LinearEquiv.restrictScalars_symm_apply]
  have key : ((↑(orthogonalGroupBaseChange (A := ℚ_[p]) L.norm γ * g p) :
      ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V)).symm (1 ⊗ₜ v) =
        (g p : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V).symm (1 ⊗ₜ (γ : V ≃ₗ[ℚ] V).symm v) := by
    rw [LinearEquiv.symm_apply_eq, Subgroup.coe_mul, mul_apply_eq_comp,
      LinearEquiv.apply_symm_apply, orthogonalGroupBaseChange_apply_tmul,
      LinearEquiv.apply_symm_apply]
  rw [key]

/-- The isometry `g • L ≅ γ g • L` given by a rational isometry `γ` of the quadratic space of
`L`. -/
noncomputable def adelicTranslateDiagonalIsometry (γ : orthogonalGroup L.norm) :
    Isometry (L.adelicTranslate g)
      (L.adelicTranslate (L.orthogonalCompactOpens.finiteAdelicOrthogonalDiagonal γ * g)) where
  toLinearEquiv := (γ : V ≃ₗ[ℚ] V)
  map_app' := LinearMap.BilinForm.mem_isometryGroup_iff.mp (L.orthogonalGroup_norm ▸ γ.2)
  map_carrier := (L.adelicTranslate_finiteAdelicOrthogonalDiagonal_mul_carrier g γ).symm

/-- The isometry `g • L ≅ γ g • L` is `γ` on the ambient space. -/
@[simp]
theorem adelicTranslateDiagonalIsometry_apply (γ : orthogonalGroup L.norm) (v : V) :
    L.adelicTranslateDiagonalIsometry g γ v = (γ : V ≃ₗ[ℚ] V) v :=
  (rfl)

/-- **A translate of `L` lies in the genus of `L`.** -/
theorem sameGenus_adelicTranslate : L.SameGenus (L.adelicTranslate g) := by
  refine (sameGenus_iff_localIntegralForm_equivalent (M := L.adelicTranslate g)
    ⟨.refl L.form⟩).mpr fun p _ ↦ ?_
  let q : Nat.Primes := ⟨p, Fact.out⟩
  refine (localIntegralForm_equivalent_iff_exists_isometryEquiv p).mpr ?_
  rw [adelicTranslate_completedRationalForm]
  refine ⟨(L.completedRationalForm p).isometryGroupEquivIsometryEquiv
      ⟨g q, L.orthogonalGroup_norm_baseChange p ▸ (g q).2⟩, fun x ↦ ?_⟩
  rw [L.range_localizationToCompletion, (L.adelicTranslate g).range_localizationToCompletion]
  have hq := L.padicLocalization_adelicTranslate_carrier g q
  dsimp only [q] at hq
  rw [hq, LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv]
  exact apply_mem_localTranslate_iff

/-- **Every lattice on the quadratic space of `L` in the genus of `L` is a translate of `L`.** -/
theorem exists_adelicTranslate_eq {M : IntegralLattice V} (hform : M.form = L.form)
    (hM : L.SameGenus M) : ∃ g, L.adelicTranslate g = M := by
  -- At every prime an integral local isometry `L_p ≅ M_p` extends to `k_p ∈ O(V_p)`.
  have hk (p : Nat.Primes) : ∃ k : orthogonalGroup (L.norm.baseChange ℚ_[p]),
      L.localTranslate p k = M.carrier.padicLocalization p := by
    have hc : M.completedRationalForm p = L.completedRationalForm p := by
      rw [completedRationalForm_def, completedRationalForm_def, hform]
    have h := (localIntegralForm_equivalent_iff_exists_isometryEquiv p).mp
      (hM.localIntegralForm_equivalent p)
    rw [hc, L.range_localizationToCompletion p, M.range_localizationToCompletion p] at h
    obtain ⟨φ, hφ⟩ := h
    refine ⟨(MulEquiv.subgroupCongr (L.orthogonalGroup_norm_baseChange p)).symm
      ((L.completedRationalForm p).isometryGroupEquivIsometryEquiv.symm φ),
      localTranslate_eq_iff.mpr fun x ↦ ?_⟩
    rw [MulEquiv.subgroupCongr_symm_apply,
      LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm]
    exact hφ x
  choose k hk using hk
  -- Where `M_p = L_p`, the isometry `k_p` lies in `K_p(L)`.
  have hev : ∀ᶠ p : Nat.Primes in cofinite, k p ∈ L.orthogonalCompactOpens.orthogonal p := by
    filter_upwards [Submodule.eventually_padicLocalization_eq (N := M.carrier) L.carrier]
      with p hp
    rw [L.orthogonalCompactOpens_orthogonal, L.mem_localStabilizer_iff_localTranslate_eq, hk, hp]
  refine ⟨⟨k, hev⟩, IntegralLattice.ext ?_ hform.symm⟩
  refine (Submodule.eq_iff_forall_padicLocalization_eq _).mpr fun p ↦ ?_
  exact (L.padicLocalization_adelicTranslate_carrier _ p).trans (hk p)

end AdelicTranslate

section DoubleCoset

/-- **The class of the translates of `L` by a double coset.** The isometry class of `g • L`
depends only on the double coset of `g` in `O(V)(ℚ) \ O(V)(𝔸_f) / K_f(L)`. -/
noncomputable def doubleCosetClass :
    L.orthogonalCompactOpens.finiteAdelicOrthogonalDoubleCoset → IsometryQuotient V :=
  Quotient.lift (fun g ↦ (L.adelicTranslate g).isometryClass) fun g h hgh ↦ by
    obtain ⟨_, ⟨γ, rfl⟩, k, hk, rfl⟩ := DoubleCoset.rel_iff.mp hgh
    have h : L.adelicTranslate (L.orthogonalCompactOpens.finiteAdelicOrthogonalDiagonal γ * g * k) =
        L.adelicTranslate (L.orthogonalCompactOpens.finiteAdelicOrthogonalDiagonal γ * g) := by
      rw [adelicTranslate_eq_adelicTranslate_iff, mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem hk
    rw [h]
    exact (L.adelicTranslateDiagonalIsometry g γ).isometryClass_eq

/-- The class of the double coset of `g` is the class of `g • L`. -/
@[simp]
theorem doubleCosetClass_mk (g : L.orthogonalCompactOpens.finiteAdelicOrthogonal) :
    L.doubleCosetClass (DoubleCoset.mk _ _ g) = (L.adelicTranslate g).isometryClass :=
  (rfl)

/-- Every class of the form `doubleCosetClass` lies in the genus of `L`. -/
theorem doubleCosetClass_mem_genusClasses
    (c : L.orthogonalCompactOpens.finiteAdelicOrthogonalDoubleCoset) :
    L.doubleCosetClass c ∈ L.genusClasses := by
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective c
  exact isometryClass_mem_genusClasses_iff.mpr (L.sameGenus_adelicTranslate g)

/-- **Distinct double cosets give non-isometric translates of `L`**: `g • L` and `h • L` are
isometric only when `g` and `h` lie in the same double coset `O(V)(ℚ) g K_f(L)`. -/
theorem doubleCosetClass_injective : Function.Injective L.doubleCosetClass := by
  intro c d hcd
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective c
  obtain ⟨h, rfl⟩ := Quotient.mk_surjective d
  obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp hcd
  let γ : orthogonalGroup L.norm := (MulEquiv.subgroupCongr L.orthogonalGroup_norm).symm
    (L.form.isometryGroupEquivIsometryEquiv.symm e.toIsometryEquiv)
  have hγe : (γ : V ≃ₗ[ℚ] V) = e.toLinearEquiv := LinearEquiv.ext <| congrFun
    (L.form.coe_isometryGroupEquivIsometryEquiv_symm e.toIsometryEquiv)
  have hγ : L.adelicTranslate (L.orthogonalCompactOpens.finiteAdelicOrthogonalDiagonal γ * g) =
      L.adelicTranslate h :=
    IntegralLattice.ext ((L.adelicTranslate_finiteAdelicOrthogonalDiagonal_mul_carrier g γ).trans
      (hγe ▸ e.map_carrier)) rfl
  refine DoubleCoset.eq.mpr ⟨_, ⟨γ, rfl⟩, _, (L.adelicTranslate_eq_adelicTranslate_iff).mp hγ, ?_⟩
  group

/-- **The classes of the double cosets are the classes of the genus of `L` represented on the
quadratic space of `L`.** -/
theorem mem_range_doubleCosetClass_iff {c : IsometryQuotient V} :
    c ∈ Set.range L.doubleCosetClass ↔
      ∃ M : IntegralLattice V, M.form = L.form ∧ L.SameGenus M ∧ M.isometryClass = c := by
  refine ⟨?_, fun ⟨M, hform, hM, hc⟩ ↦ ?_⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨g, rfl⟩ := Quotient.mk_surjective d
    exact ⟨L.adelicTranslate g, rfl, L.sameGenus_adelicTranslate g, rfl⟩
  · obtain ⟨g, rfl⟩ := L.exists_adelicTranslate_eq hform hM
    exact ⟨DoubleCoset.mk _ _ g, hc⟩

end DoubleCoset

end IntegralLattice

end TauCeti
