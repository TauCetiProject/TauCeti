/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.RingTheory.NovikovModule.Topology
public import TauCeti.RingTheory.NovikovSeries.Localization

/-!
# Shifted lattices of completed Novikov modules

Let `S = Σ i, P i` be a finite disjoint union of torsors under an additive group `H`, with a
potential `F : S → ℝ` satisfying `F (h +ᵥ p) = F p - N h` for a period map `N : H →+ ℝ`. The
completed combinations `NovikovModule R F` form a finite free module over the Novikov ring
`Λ = Nov(R, H, N)` (`TauCeti.NovikovModule.module`). The *valuation* of a generator `p` is
`-F p`, so multiplying by a monomial `e^h` of positive period raises valuations by `N h`.

For a real number `C`, the completed combinations vanishing at every generator of potential
`> C`, that is, those all of whose generators have valuation at least `-C`, form the subgroup
`U_C` of the potential-cutoff topology (`TauCeti.NovikovModule.potentialFiltration`). This file
shows that `U_C` is a module over the nonnegative subring `Λ₀` of Novikov series, the *shifted
lattice* `lattice R hF C` of cutoff `C` (`TauCeti.NovikovModule.lattice`), and develops its basic
properties:

* the lattices increase with the cutoff, so that `C ≤ D` gives the injective inclusion
  `Submodule.inclusion : lattice R hF C → lattice R hF D`; they exhaust the completed combinations,
  and meet only in `0`;
* the monomial `e^h` maps `lattice R hF (C + N h)` onto `lattice R hF C`;
* if the monomials `e^m`, `m ∈ M`, have periods unbounded above, then the inclusion of any
  lattice is a localization at these monomials: the completed module over the full Novikov ring
  is obtained from a single lattice by inverting them. In the action-weighted case, with
  exponents `G × ℝ`, periods `(g, t) ↦ E g + t` and the monomials `T^t = e^(0, t)`, `t ≥ 0`,
  this says that the completed module is `⋃ₜ T^(-t) (lattice R hF 0)`, and
  `T^(-t) (lattice R hF 0) = lattice R hF t`;
* chosen lifts `r` all of potential `C` form a basis of `lattice R hF C` over `Λ₀`. When the period
  map is surjective, as in the action-weighted case, such lifts always exist, so each lattice is
  a finite free `Λ₀`-module.

The localization statement is Mathlib's `IsLocalizedModule`, so its universal property applies:
a `Λ₀`-linear map out of a lattice into a module on which the monomials act invertibly extends
uniquely to the completed module (`IsLocalizedModule.lift`). Over `Λ₀` the lattices are genuinely
different from the completed module, since the monomials of positive period are not units of
`Λ₀` (`TauCeti.NovikovSeries.posIdeal_ne_top`): a chain homotopy over the localized module need
not restrict to one on a lattice without a shift of the cutoff.

## Main definitions

* `TauCeti.NovikovModule.lattice R hF C`: the completed combinations of valuation at least `-C`, as
  a submodule over the nonnegative subring of Novikov series.
* `TauCeti.NovikovModule.latticeBasis hF r hr`: the basis of `lattice R hF C` given by lifts `r`
  all of potential `C`.

## Main results

* `TauCeti.NovikovModule.single_smul_mem_lattice_iff`:
  `e^h • a ∈ lattice R hF C ↔ a ∈ lattice R hF (C + N h)`, and its set-level form
  `TauCeti.NovikovModule.single_smul_lattice`: `e^h • lattice R hF C = lattice R hF (C - N h)`.
* `TauCeti.NovikovModule.biUnion_single_neg_smul_lattice`: for monomials of unbounded period, the
  completed combinations are `⋃ₘ e^(-m) (lattice R hF C)`; in the action-weighted case,
  `TauCeti.NovikovModule.single_inr_neg_smul_lattice_zero` and
  `TauCeti.NovikovModule.biUnion_single_inr_neg_smul_lattice_zero` give
  `T^(-t) (lattice R hF 0) = lattice R hF t` and that the completed combinations are
  `⋃_(t ≥ 0) T^(-t) (lattice R hF 0)`.
* `TauCeti.NovikovModule.iUnion_lattice`, `TauCeti.NovikovModule.iInf_lattice`: the lattices
  exhaust the completed combinations and meet in `0`.
* `TauCeti.NovikovModule.isLocalizedModule_lattice`: the inclusion of a lattice is a localization
  at monomials of unbounded period.
* `TauCeti.NovikovModule.isLocalizedModule_lattice_map_inr`: in the action-weighted case, the
  inclusion of a lattice is a localization at the monomials `T^r`, `r ≥ 0`.
* `TauCeti.NovikovModule.free_lattice`, `TauCeti.NovikovModule.finite_lattice`: for a surjective
  period map, each lattice is a finite free module over the nonnegative subring.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009 (filtered modules over
  the universal Novikov ring `Λ₀` and their localization at the monomials `T^λ`).
-/

public section

noncomputable section

namespace TauCeti.NovikovModule

open NovikovSeries
open scoped Pointwise

section Ring

variable {R H ι : Type*} [Ring R] [AddGroup H] [Finite ι] {P : ι → Type*}
    [∀ i, AddTorsor H (P i)] {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)

variable (R) in
/-- The **shifted lattice** of cutoff `C`: the completed combinations whose coefficients vanish at
every generator of potential `> C`, that is, of valuation `< -C`, as a module over the
nonnegative subring of Novikov series. Its underlying additive subgroup is
`potentialFiltration R F C`. -/
def lattice (C : ℝ) :
    letI := module (R := R) hF
    Submodule (nonnegSubring R N) (NovikovModule R F) :=
  letI := module (R := R) hF
  { potentialFiltration R F C with
    smul_mem' b a ha := by
      rw [Subring.smul_def, ← sub_zero C]
      exact smul_mem_potentialFiltration_sub hF
        (mem_periodFiltration.2 (mem_nonnegSubring.1 b.property)) ha }

variable {C D : ℝ} {a : NovikovModule R F}

/-- A completed combination lies in the lattice of cutoff `C` exactly when it vanishes at every
generator of potential `> C`. -/
@[simp]
theorem mem_lattice : a ∈ lattice R hF C ↔ a ∈ potentialFiltration R F C :=
  Iff.rfl

/-- The underlying additive subgroup of the lattice of cutoff `C` is the subgroup `U_C` of the
potential filtration. -/
theorem toAddSubgroup_lattice (C : ℝ) :
    (lattice R hF C).toAddSubgroup = potentialFiltration R F C :=
  (rfl)

/-- The lattices increase with the cutoff. For `C ≤ D` the inclusion of the lattice of cutoff `C`
into that of cutoff `D` is `Submodule.inclusion (monotone_lattice hF h)`. -/
theorem monotone_lattice : Monotone (lattice R hF) :=
  fun _ _ h _ ha => monotone_potentialFiltration h ha

/-- The lattices exhaust the completed combinations: every completed combination has valuation
bounded below. -/
theorem iUnion_lattice : ⋃ C, (lattice R hF C : Set (NovikovModule R F)) = Set.univ :=
  Set.eq_univ_of_forall fun a => Set.mem_iUnion.2 (exists_mem_potentialFiltration a)

/-- The lattices meet only in `0`. -/
theorem iInf_lattice :
    letI := module (R := R) hF
    ⨅ C, lattice R hF C = ⊥ :=
  letI := module (R := R) hF
  eq_bot_iff.2 fun _ ha => (Submodule.mem_bot _).2 <|
    eq_zero_of_forall_mem_potentialFiltration fun C => Submodule.mem_iInf _ |>.1 ha C

/-- **Shifting lattices by monomials.** Multiplication by the monomial `e^h` maps the lattice of
cutoff `C + N h` onto that of cutoff `C`: it lowers potentials, and raises valuations, by the
period `N h`. -/
theorem single_smul_mem_lattice_iff (h : H) :
    letI := module (R := R) hF
    NovikovSeries.single (N := N) h (1 : R) • a ∈ lattice R hF C ↔
      a ∈ lattice R hF (C + N h) := by
  let := module (R := R) hF
  simp only [mem_lattice, mem_potentialFiltration]
  constructor
  · rintro ha ⟨i, p⟩ hp
    have := ha ⟨i, h +ᵥ p⟩ (by rw [hF]; linarith)
    rwa [single_smul_apply hF, neg_vadd_vadd, one_mul] at this
  · rintro ha ⟨i, p⟩ hp
    rw [single_smul_apply hF, ha ⟨i, -h +ᵥ p⟩ (by rw [hF, map_neg]; linarith), mul_zero]

/-- **Monomial shifts of lattices.** The monomial `e^h` maps the lattice of cutoff `C` onto that
of cutoff `C - N h`. -/
theorem single_smul_lattice (h : H) (C : ℝ) :
    letI := module (R := R) hF
    NovikovSeries.single (N := N) h (1 : R) • (lattice R hF C : Set (NovikovModule R F)) =
      lattice R hF (C - N h) := by
  let := module (R := R) hF
  ext a
  refine ⟨?_, fun ha => ⟨NovikovSeries.single (N := N) (-h) (1 : R) • a, ?_, ?_⟩⟩
  · rintro ⟨b, hb, rfl⟩
    exact (single_smul_mem_lattice_iff hF h).2 (by rwa [sub_add_cancel])
  · exact (single_smul_mem_lattice_iff hF (-h)).2 (by rwa [map_neg, ← sub_eq_add_neg])
  · simp only [smul_smul, single_mul_single, add_neg_cancel, mul_one, single_zero_one, one_smul]

/-- **The completed module as a union of shifted lattices.** If the monomials `e^m`, `m ∈ M`, have
periods unbounded above, then every completed combination lies in `e^(-m)` times the lattice of
cutoff `C` for some `m ∈ M`. -/
theorem biUnion_single_neg_smul_lattice {M : Set H} (hM : ∀ D : ℝ, ∃ m ∈ M, D ≤ N m) (C : ℝ) :
    letI := module (R := R) hF
    ⋃ m ∈ M, NovikovSeries.single (N := N) (-m) (1 : R) •
      (lattice R hF C : Set (NovikovModule R F)) = Set.univ := by
  let := module (R := R) hF
  refine Set.eq_univ_of_forall fun a => ?_
  obtain ⟨D, hD⟩ := exists_mem_potentialFiltration a
  obtain ⟨m, hmM, hm⟩ := hM (D - C)
  simp only [Set.mem_iUnion, single_smul_lattice, map_neg, sub_neg_eq_add]
  exact ⟨m, hmM, monotone_lattice hF (by linarith) hD⟩

/-- Lifts all of potential `C` identify the lattice of cutoff `C` with `ι → Λ₀`, by their
coordinates. -/
def latticeEquiv (r : ∀ i, P i) (hr : ∀ i, F ⟨i, r i⟩ = C) :
    letI := module (R := R) hF
    lattice R hF C ≃ₗ[nonnegSubring R N] (ι → nonnegSubring R N) :=
  letI := module (R := R) hF
  { toFun a i := ⟨coordinates hF r a i, by
      have := (mem_potentialFiltration_iff_coordinates hF r).1 a.property i
      rw [hr, sub_self] at this
      exact mem_nonnegSubring.2 (mem_periodFiltration.1 this)⟩
    invFun b := ⟨(coordinates hF r).symm fun i => b i, by
      refine (mem_potentialFiltration_iff_coordinates hF r).2 fun i => ?_
      rw [LinearEquiv.apply_symm_apply, hr, sub_self]
      exact mem_periodFiltration.2 (mem_nonnegSubring.1 (b i).property)⟩
    left_inv a := by
      ext1
      simp
    right_inv b := by
      ext1 i
      simp
    map_add' a b := by
      ext1 i
      simp
    map_smul' c a := by
      funext i
      exact Subtype.ext (by simp [Subring.smul_def, coordinates_smul hF r]) }

/-- The coordinates of an element of a lattice in lifts of potential `C` are its Novikov
coordinates. -/
@[simp]
theorem coe_latticeEquiv_apply (r : ∀ i, P i) (hr : ∀ i, F ⟨i, r i⟩ = C) (a : lattice R hF C)
    (i : ι) : (latticeEquiv hF r hr a i : NovikovSeries R H N) = coordinates hF r a i :=
  (rfl)

/-- The inverse of `latticeEquiv` reconstructs the completed combination from its coordinates. -/
@[simp]
theorem coe_latticeEquiv_symm_apply (r : ∀ i, P i) (hr : ∀ i, F ⟨i, r i⟩ = C)
    (b : ι → nonnegSubring R N) :
    letI := module (R := R) hF
    ((latticeEquiv hF r hr).symm b : NovikovModule R F) =
      (coordinates hF r).symm fun i => (b i : NovikovSeries R H N) :=
  (rfl)

/-- The basis of the lattice of cutoff `C` over the nonnegative subring formed by lifts `r` all
of potential `C`. -/
def latticeBasis (r : ∀ i, P i) (hr : ∀ i, F ⟨i, r i⟩ = C) :
    letI := module (R := R) hF
    Module.Basis ι (nonnegSubring R N) (lattice R hF C) :=
  letI := module (R := R) hF
  .ofEquivFun (latticeEquiv hF r hr)

/-- The basis vectors of a lattice are the lifts, as basis vectors of the completed module. -/
@[simp]
theorem coe_latticeBasis (r : ∀ i, P i) (hr : ∀ i, F ⟨i, r i⟩ = C) (i : ι) :
    (latticeBasis (R := R) hF r hr i : NovikovModule R F) = basis hF r i := by
  classical
  apply (coordinates hF r).injective
  ext1 j
  rcases eq_or_ne j i with rfl | hji <;> simp [latticeBasis, *]

/-- The coordinates of an element of a lattice in the basis of lifts are its Novikov
coordinates. -/
@[simp]
theorem coe_latticeBasis_repr_apply (r : ∀ i, P i) (hr : ∀ i, F ⟨i, r i⟩ = C)
    (a : lattice R hF C) (i : ι) :
    ((latticeBasis hF r hr).repr a i : NovikovSeries R H N) = coordinates hF r a i := by
  simp [latticeBasis]

omit [Finite ι] in
include hF in
/-- If the period map is surjective, every orbit has a generator of any prescribed potential:
translate any generator by an element of period `F p - C`. -/
theorem exists_potential_eq (hN : Function.Surjective N) (i : ι) (C : ℝ) :
    ∃ p : P i, F ⟨i, p⟩ = C := by
  obtain ⟨p⟩ : Nonempty (P i) := inferInstance
  obtain ⟨h, hh⟩ := hN (F ⟨i, p⟩ - C)
  exact ⟨h +ᵥ p, by rw [hF, hh, sub_sub_cancel]⟩

/-- If the period map is surjective, each lattice is a free module over the nonnegative subring,
on lifts of potential `C`. This applies in the action-weighted case, with exponents `G × ℝ` and
periods `(g, t) ↦ E g + t`. -/
theorem free_lattice (hN : Function.Surjective N) (C : ℝ) :
    letI := module (R := R) hF
    Module.Free (nonnegSubring R N) (lattice R hF C) := by
  let := module (R := R) hF
  choose r hr using fun i => exists_potential_eq hF hN i C
  exact .of_basis (latticeBasis hF r hr)

/-- If the period map is surjective, each lattice is a finitely generated module over the
nonnegative subring. -/
theorem finite_lattice (hN : Function.Surjective N) (C : ℝ) :
    letI := module (R := R) hF
    Module.Finite (nonnegSubring R N) (lattice R hF C) := by
  let := module (R := R) hF
  choose r hr using fun i => exists_potential_eq hF hN i C
  exact .of_basis (latticeBasis hF r hr)

/-- **Action-weighted shifted lattices.** On the exponent group `G × ℝ` with periods
`(g, t) ↦ E g + t`, the monomial `T^(-t) = e^(0, -t)` maps the lattice of cutoff `0` onto that of
cutoff `t`. -/
theorem single_inr_neg_smul_lattice_zero {G : Type*} [AddGroup G] {E : G →+ ℝ}
    {P : ι → Type*} [∀ i, AddTorsor (G × ℝ) (P i)] {F : (Σ i, P i) → ℝ}
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - E.coprod (AddMonoidHom.id ℝ) h) (t : ℝ) :
    letI := module (R := R) hF
    NovikovSeries.single (N := E.coprod (AddMonoidHom.id ℝ)) (AddMonoidHom.inr G ℝ (-t)) (1 : R) •
      (lattice R hF 0 : Set (NovikovModule R F)) = lattice R hF t := by
  rw [single_smul_lattice]
  simp

/-- **The action-weighted completed module as a union of shifted lattices.** On the exponent
group `G × ℝ` with periods `(g, t) ↦ E g + t`, every completed combination lies in
`T^(-t) (lattice R hF 0)` for some `t ≥ 0`, where `T^(-t) = e^(0, -t)`. -/
theorem biUnion_single_inr_neg_smul_lattice_zero {G : Type*} [AddGroup G] {E : G →+ ℝ}
    {P : ι → Type*} [∀ i, AddTorsor (G × ℝ) (P i)] {F : (Σ i, P i) → ℝ}
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - E.coprod (AddMonoidHom.id ℝ) h) :
    letI := module (R := R) hF
    ⋃ t ≥ (0 : ℝ),
      NovikovSeries.single (N := E.coprod (AddMonoidHom.id ℝ)) (AddMonoidHom.inr G ℝ (-t)) (1 : R) •
        (lattice R hF 0 : Set (NovikovModule R F)) = Set.univ := by
  refine Set.eq_univ_of_forall fun a => ?_
  obtain ⟨D, hD⟩ := exists_mem_potentialFiltration a
  simp only [Set.mem_iUnion, single_inr_neg_smul_lattice_zero]
  exact ⟨max D 0, le_max_right _ _, monotone_lattice hF (le_max_left _ _) hD⟩

end Ring

section CommRing

variable {R H ι : Type*} [CommRing R] [AddCommGroup H] [Finite ι] {P : ι → Type*}
    [∀ i, AddTorsor H (P i)] {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)

/-- **The completed module as a localization of a lattice.** If the monomials `e^m`, `m ∈ M`,
have periods unbounded above, then the inclusion of any lattice into the completed combinations
is a localization at these monomials. The hypothesis cannot be dropped: for `N = 0`
every lattice below the least potential of a generator is zero. -/
theorem isLocalizedModule_lattice {M : AddSubmonoid H} (hM : ∀ D : ℝ, ∃ m ∈ M, D ≤ N m)
    (C : ℝ) :
    letI := module (R := R) hF
    IsLocalizedModule (monomialSubmonoid R N M) (lattice R hF C).subtype := by
  let := module (R := R) hF
  refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by simpa using h⟩⟩
  · -- A monomial is a unit of the Novikov ring, so it acts bijectively.
    obtain ⟨m, -, hs⟩ := mem_monomialSubmonoid.1 s.property
    obtain ⟨u, hu⟩ := isUnit_single (N := N) m (isUnit_one (M := R))
    have hsu : ⇑(algebraMap (nonnegSubring R N) (Module.End (nonnegSubring R N) _) s) =
        (u • · : NovikovModule R F → NovikovModule R F) := by
      funext y
      rw [Module.algebraMap_end_apply, Units.smul_def, hu, Submonoid.smul_def, ← hs]
    rw [Module.End.isUnit_iff, hsu]
    exact MulAction.bijective u
  · -- Multiply by a monomial of period large enough to move `y` into the lattice.
    obtain ⟨D, hD⟩ := exists_mem_potentialFiltration y
    obtain ⟨m, hmM, hm⟩ := hM (max (D - C) 0)
    have hm₀ : 0 ≤ N m := (le_max_right _ _).trans hm
    refine ⟨(⟨NovikovSeries.single m 1 • y, (single_smul_mem_lattice_iff hF m).2 <|
      monotone_lattice hF (by linarith [le_max_left (D - C) 0]) hD⟩,
      ⟨_, single_mem_monomialSubmonoid hmM hm₀⟩), ?_⟩
    rw [Submonoid.smul_def, Subring.smul_def, Submodule.subtype_apply]

/-- **Action-weighted localization of a lattice.** On the exponent group `G × ℝ` with periods
`(g, r) ↦ E g + r`, the inclusion of any lattice is a localization at the monomials
`T^r = e^(0, r)`, `r ≥ 0`. The corresponding set-level identities
`T^(-r) (lattice R hF 0) = lattice R hF r` and `⋃_(r ≥ 0) T^(-r) (lattice R hF 0) = univ` are
`single_inr_neg_smul_lattice_zero` and `biUnion_single_inr_neg_smul_lattice_zero`. -/
theorem isLocalizedModule_lattice_map_inr {G : Type*} [AddCommGroup G] {E : G →+ ℝ}
    {P : ι → Type*} [∀ i, AddTorsor (G × ℝ) (P i)] {F : (Σ i, P i) → ℝ}
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - E.coprod (AddMonoidHom.id ℝ) h) (C : ℝ) :
    letI := module (R := R) hF
    IsLocalizedModule
      (monomialSubmonoid R (E.coprod (AddMonoidHom.id ℝ))
        ((AddSubmonoid.nonneg ℝ).map (AddMonoidHom.inr G ℝ)))
      (lattice R hF C).subtype :=
  isLocalizedModule_lattice (M := (AddSubmonoid.nonneg ℝ).map (AddMonoidHom.inr G ℝ)) hF
    (fun D => ⟨(0, max D 0), ⟨_, le_max_right _ _, rfl⟩, by simp⟩) C

end CommRing

end TauCeti.NovikovModule
