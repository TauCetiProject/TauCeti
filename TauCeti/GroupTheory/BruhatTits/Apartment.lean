/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.Algebra.Torsor.Basic
public import TauCeti.GroupTheory.BruhatTits.Valuation
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.Basic
import Mathlib.Tactic.Module

/-!
# The apartment of a valued root datum

Let `D` be a root datum of type `P` in a group `G`, with real root pairing
`P : RootPairing ι ℝ M N`, and let `φ : Valuation D` be a valuation of `D`. Shifting `φ` by vectors
`v : N` of the coweight space produces the equipollence class `{φ.shift v | v : N}` of `φ`, which
is the *reduced apartment* attached to `φ`. When the roots do not span `M` (for instance, for a
non-semisimple reductive group with positive-dimensional split center), the shift action of `N` on
`Valuation D` has non-trivial kernel `⨅ i, ker (P.root' i)`, whereas functoriality in `G` requires
an honest affine space with translation space `N`.

Accordingly, following Bruhat–Tits (I, 6.2.5 and II, 4.2.16), the *(enlarged) apartment*
`Apartment φ` attached to `φ` is defined as the type of pairs `(ψ, v)` consisting of a valuation
`ψ : Valuation D` and a displacement vector `v : N` witnessing `ψ = φ.shift v`. It carries:

* a free and transitive additive action of `N` (`Apartment.instAddTorsor`), hence no privileged
  translation-invariant origin when `N` is nontrivial
  (`TauCeti.AddTorsor.not_exists_forall_vadd_eq_self`);
* the projection `Apartment.val : Apartment φ → Valuation D` onto the equipollence class of `φ`
  (`Apartment.range_val`), whose fibers are cosets of the central subspace `⨅ i, ker (P.root' i)`
  (`Apartment.val_eq_val_iff`) and which is injective when `P.rootSpan ℝ = ⊤`
  (`Apartment.val_injective_of_rootSpan_eq_top`, `Apartment.val_injective`);
* canonical affine equivalences `Apartment.transport x₀ : Apartment φ ≃ᵃ[ℝ] Apartment x₀.val`
  relating apartments based at equipollent valuations while preserving the underlying valuation and
  pointwise filtrations (`Apartment.transport_val`, `Apartment.filtrationAt_transport`);
* pointwise root-group filtrations `x.filtrationAt i r = x.val.filtration i r`, which translate
  by `(v +ᵥ x).filtrationAt i r = x.filtrationAt i (r - P.root' i v)` and detect `x.val`
  (`Apartment.forall_filtrationAt_eq_iff_val_eq`);
* an apartment-geometric reformulation of torus compatibility
  (`Valuation.IsCompatible.conj_smul_filtrationAt`, `Valuation.isCompatible_iff_filtrationAt`): `φ`
  is compatible with `ν : D.T → N` if and only if conjugation by each `z ∈ D.T` translates the
  pointwise root-group filtrations by `ν z`;
* the *wall reflections* `Apartment.wallReflection φ i k : Apartment φ ≃ᵃ[ℝ] Apartment φ` in the
  affine hyperplanes `{x | P.root' i (x -ᵥ base φ) + k = 0}`, which realize conjugation of the
  rank-one filtration subgroups by elements `u' u u'' ∈ M a` with `φ a u = k`
  (`Apartment.conj_smul_filtrationAt_reflectionPerm`).

## Main definitions

* `TauCeti.BruhatTits.Apartment`: the enlarged apartment attached to a valuation `φ : Valuation D`.
* `TauCeti.BruhatTits.Apartment.ofDisplacement`, `TauCeti.BruhatTits.Apartment.base`: point at
  displacement `v : N` from `φ`, and the base point at `0`.
* `TauCeti.BruhatTits.Apartment.instAddTorsor`: the `AddTorsor N (Apartment φ)` structure.
* `TauCeti.BruhatTits.Apartment.congr`, `TauCeti.BruhatTits.Apartment.transport`: affine
  equivalences induced by equality of base valuations and by changing the base point to `x₀`.
* `TauCeti.BruhatTits.Apartment.filtrationAt`: the root-group filtration subgroup `U_x(a, r)`
  attached to a point `x : Apartment φ`, root `a`, and real threshold `r`.
* `TauCeti.BruhatTits.Apartment.wallReflection`: the affine reflection of `Apartment φ` across the
  hyperplane `a(x -ᵥ base φ) + k = 0`.

## Main results

* `TauCeti.BruhatTits.Apartment.range_val`: the image of `Apartment.val` is `{ψ | φ.Equipollent ψ}`.
* `TauCeti.BruhatTits.Apartment.val_eq_val_iff`, `TauCeti.BruhatTits.Apartment.val_injective`:
  `x.val = y.val` iff every root vanishes on `x -ᵥ y`; when `[P.IsRootSystem]`, `val` is injective.
* `TauCeti.BruhatTits.Apartment.transport_trans`: cocycle compatibility of base-point changes.
* `TauCeti.BruhatTits.Apartment.forall_filtrationAt_eq_iff_val_eq`: two points have the same
  pointwise root-group filtrations iff they have the same underlying valuation.
* `TauCeti.BruhatTits.Valuation.isCompatible_iff_filtrationAt`,
  `TauCeti.BruhatTits.Valuation.IsCompatible.eq`: apartment characterization of `φ.IsCompatible ν`,
  and uniqueness of `ν` when `[P.IsRootSystem]`.
* `TauCeti.BruhatTits.Apartment.wallReflection_apply_eq_self_iff`,
  `TauCeti.BruhatTits.Apartment.transport_wallReflection`,
  `TauCeti.BruhatTits.Apartment.conj_smul_filtrationAt_reflectionPerm`: fixed-point hyperplane,
  base-point invariance, and rank-one filtration conjugation for wall reflections.

## Implementation notes

Packaging both `val : Valuation D` and `displacement : N` with `val_eq : val = φ.shift displacement`
gives `Apartment φ` a faithful `N`-torsor structure without assuming `P.IsRootSystem`, while making
the forgetful map `Apartment.val` to the reduced apartment a field projection. Characteristic
projection lemmas use `:= (rfl)` so downstream modules never rely on private definitional equality.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  6.2.5–6.2.7, pp. 120–121, and 6.2.10, p. 122.
* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  4.2.16, p. 94.
-/

public section

open scoped Pointwise commutatorElement

namespace TauCeti.BruhatTits

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {G : Type*} [Group G] {P : RootPairing ι ℝ M N} {D : RootDatum P G}

/-- If the roots span `M` over `ℝ`, a coweight annihilated by every root functional is `0`. -/
private theorem eq_zero_of_forall_root'_eq_zero (hP : P.rootSpan ℝ = ⊤) {v : N}
    (hv : ∀ i : ι, P.root' i v = 0) : v = 0 := by
  have hmem : v ∈ ⨅ i, LinearMap.ker (P.root' i) := (Submodule.mem_iInf _).mpr hv
  simpa [← P.rootSpan_dualAnnihilator_map_eq_iInf_ker_root', hP] using hmem

/-- The (enlarged) apartment attached to a valuation `φ` of a root datum `D`: a point consists of a
valuation `val` equipollent to `φ` together with a displacement vector `displacement : N`
witnessing `val = φ.shift displacement`. -/
structure Apartment (φ : Valuation D) where
  /-- The root-datum valuation at this point of the apartment. -/
  val : Valuation D
  /-- The displacement vector from the base valuation `φ` in the coweight space `N`. -/
  displacement : N
  /-- The valuation at this point is the shift of `φ` by `displacement`. -/
  val_eq : val = φ.shift displacement

namespace Apartment

section Basic

variable {φ ψ χ : Valuation D}

@[ext]
theorem ext {x y : Apartment φ} (h : x.displacement = y.displacement) : x = y := by
  cases x with | mk vx dx hx =>
  cases y with | mk vy dy hy =>
  subst h hx
  simp [hy]

theorem displacement_injective : Function.Injective (displacement (φ := φ)) :=
  fun _ _ ↦ ext

@[simp]
theorem displacement_inj {x y : Apartment φ} : x.displacement = y.displacement ↔ x = y :=
  displacement_injective.eq_iff

/-- The point of `Apartment φ` at displacement `v : N` from `φ`. -/
def ofDisplacement (φ : Valuation D) (v : N) : Apartment φ where
  val := φ.shift v
  displacement := v
  val_eq := rfl

@[simp]
theorem ofDisplacement_val (φ : Valuation D) (v : N) : (ofDisplacement φ v).val = φ.shift v :=
  (rfl)

@[simp]
theorem ofDisplacement_displacement (φ : Valuation D) (v : N) :
    (ofDisplacement φ v).displacement = v :=
  (rfl)

theorem ofDisplacement_injective : Function.Injective (ofDisplacement φ) :=
  fun _ _ h ↦ congrArg displacement h

@[simp]
theorem ofDisplacement_inj {v w : N} : ofDisplacement φ v = ofDisplacement φ w ↔ v = w :=
  ofDisplacement_injective.eq_iff

@[simp]
theorem ofDisplacement_displacement_self (x : Apartment φ) :
    ofDisplacement φ x.displacement = x :=
  ext rfl

/-- The base point of `Apartment φ`, with valuation `φ` and zero displacement. -/
def base (φ : Valuation D) : Apartment φ where
  val := φ
  displacement := 0
  val_eq := φ.shift_zero.symm

@[simp]
theorem base_val (φ : Valuation D) : (base φ).val = φ :=
  (rfl)

@[simp]
theorem base_displacement (φ : Valuation D) : (base φ).displacement = 0 :=
  (rfl)

@[simp]
theorem ofDisplacement_zero (φ : Valuation D) : ofDisplacement φ 0 = base φ :=
  ext rfl

@[simp]
theorem displacement_eq_zero_iff {x : Apartment φ} : x.displacement = 0 ↔ x = base φ := by
  rw [← base_displacement φ, displacement_inj]

@[simp]
theorem ofDisplacement_eq_base_iff {v : N} : ofDisplacement φ v = base φ ↔ v = 0 := by
  rw [← displacement_inj, ofDisplacement_displacement, base_displacement]

instance : Inhabited (Apartment φ) :=
  ⟨base φ⟩

instance [Subsingleton N] : Unique (Apartment φ) where
  default := base φ
  uniq _ := ext (Subsingleton.elim _ _)

/-- Evaluating the valuation at `x : Apartment φ` shifts `φ` by `P.root' i x.displacement`. -/
theorem val_apply (x : Apartment φ) (i : ι) (u : D.U i) :
    x.val i u = φ i u + (P.root' i x.displacement : WithTop ℝ) := by
  rw [x.val_eq, Valuation.shift_apply]

/-- Every point of `Apartment φ` has valuation equipollent to `φ`. -/
theorem equipollent_val (x : Apartment φ) : φ.Equipollent x.val :=
  x.val_eq ▸ φ.equipollent_shift x.displacement

/-- A valuation `ψ` is equipollent to `φ` if and only if it is the valuation of a point of
`Apartment φ`. -/
theorem equipollent_iff_exists_val_eq {ψ : Valuation D} :
    φ.Equipollent ψ ↔ ∃ x : Apartment φ, x.val = ψ := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ x.equipollent_val⟩
  obtain ⟨v, hv⟩ := φ.equipollent_iff.mp h
  exact ⟨ofDisplacement φ v, Valuation.ext fun i u ↦ by
    rw [ofDisplacement_val, Valuation.shift_apply, hv]⟩

/-- The image of `Apartment.val` is the equipollence class of `φ` (the reduced apartment). -/
theorem range_val : Set.range (val (φ := φ)) = {ψ | φ.Equipollent ψ} :=
  Set.ext fun _ ↦ equipollent_iff_exists_val_eq.symm

/-- Compatibility with a map `ν : D.T → N` is constant across the apartment. -/
@[simp]
theorem isCompatible_val_iff (x : Apartment φ) {ν : D.T → N} :
    x.val.IsCompatible ν ↔ φ.IsCompatible ν := by
  rw [x.val_eq, Valuation.isCompatible_shift_iff]

/-- The value set of root `i` at `x` is the translate of `φ.valueSet i` by
`P.root' i x.displacement`. -/
theorem valueSet_val (x : Apartment φ) (i : ι) :
    x.val.valueSet i = (· + P.root' i x.displacement) '' φ.valueSet i := by
  rw [x.val_eq, Valuation.valueSet_shift]

end Basic

/-! ### Affine space structure -/

section Affine

variable {φ ψ χ : Valuation D}

/-- The coweight space `N` acts on `Apartment φ` by translating displacements and shifting
valuations. -/
instance instAddAction : AddAction N (Apartment φ) where
  vadd v x :=
    { val := x.val.shift v
      displacement := v + x.displacement
      val_eq := by rw [x.val_eq, Valuation.shift_shift, add_comm] }
  zero_vadd x := ext (zero_add x.displacement)
  add_vadd v w x := ext (add_assoc v w x.displacement)

@[simp]
theorem vadd_val (v : N) (x : Apartment φ) : (v +ᵥ x).val = x.val.shift v :=
  (rfl)

@[simp]
theorem vadd_displacement (v : N) (x : Apartment φ) :
    (v +ᵥ x).displacement = v + x.displacement :=
  (rfl)

theorem vadd_base (v : N) : v +ᵥ base φ = ofDisplacement φ v :=
  ext (add_zero v)

theorem vadd_ofDisplacement (v w : N) : v +ᵥ ofDisplacement φ w = ofDisplacement φ (v + w) :=
  ext rfl

instance instVSub : VSub N (Apartment φ) where
  vsub x y := x.displacement - y.displacement

theorem vsub_displacement (x y : Apartment φ) : x -ᵥ y = x.displacement - y.displacement :=
  (rfl)

theorem vsub_base (x : Apartment φ) : x -ᵥ base φ = x.displacement :=
  sub_zero x.displacement

theorem base_vsub (x : Apartment φ) : base φ -ᵥ x = -x.displacement :=
  zero_sub x.displacement

theorem ofDisplacement_vsub_ofDisplacement (v w : N) :
    ofDisplacement φ v -ᵥ ofDisplacement φ w = v - w :=
  (rfl)

/-- `Apartment φ` is an `ℝ`-affine space (`AddTorsor`) modeled on the coweight space `N`. -/
instance instAddTorsor : AddTorsor N (Apartment φ) where
  nonempty := ⟨base φ⟩
  vsub_vadd' x y := ext (sub_add_cancel x.displacement y.displacement)
  vadd_vsub' v x := add_sub_cancel_right v x.displacement

theorem coe_vaddConst_base : ⇑(AffineEquiv.vaddConst ℝ (base φ)) = ofDisplacement φ :=
  funext vadd_base

theorem coe_vaddConst_base_symm :
    ⇑(AffineEquiv.vaddConst ℝ (base φ)).symm = displacement (φ := φ) :=
  funext vsub_base

/-- The valuation at `x` is obtained from the valuation at `y` by shifting by `x -ᵥ y`. -/
theorem val_eq_val_shift_vsub (x y : Apartment φ) : x.val = y.val.shift (x -ᵥ y) := by
  rw [← vadd_val, vsub_vadd]

theorem val_apply_eq_add_vsub (x y : Apartment φ) (i : ι) (u : D.U i) :
    x.val i u = y.val i u + (P.root' i (x -ᵥ y) : WithTop ℝ) := by
  rw [val_eq_val_shift_vsub x y, Valuation.shift_apply]

/-! ### Reduced versus enlarged apartment -/

/-- Two points of `Apartment φ` have the same underlying valuation if and only if their difference
`x -ᵥ y` lies in the common kernel of all roots. -/
theorem val_eq_val_iff {x y : Apartment φ} :
    x.val = y.val ↔ ∀ i : ι, P.root' i (x -ᵥ y) = 0 := by
  constructor
  · intro h i
    obtain ⟨k, hk⟩ := (y.val.valueSet_nontrivial i).nonempty
    obtain ⟨u, hu⟩ := y.val.mem_valueSet_iff.mp hk
    have e := val_apply_eq_add_vsub x y i u
    rw [h, hu] at e
    norm_cast at e
    linarith
  · intro h
    ext i u
    rw [val_apply_eq_add_vsub x y i u, h i, WithTop.coe_zero, add_zero]

/-- A point `x : Apartment φ` has valuation `φ` if and only if every root vanishes on
`x.displacement`. -/
theorem val_eq_iff_forall_root'_eq {x : Apartment φ} :
    x.val = φ ↔ ∀ i : ι, P.root' i x.displacement = 0 := by
  have h := val_eq_val_iff (x := x) (y := base φ)
  rwa [base_val, vsub_base] at h

/-- When the roots span `M` over `ℝ`, the enlarged and reduced apartments coincide: `Apartment.val`
is injective. -/
theorem val_injective_of_rootSpan_eq_top (hP : P.rootSpan ℝ = ⊤) :
    Function.Injective (val (φ := φ)) := by
  intro x y h
  exact vsub_eq_zero_iff_eq.mp (eq_zero_of_forall_root'_eq_zero hP (val_eq_val_iff.mp h))

/-- For a root system (`[P.IsRootSystem]`), `Apartment.val` is injective. -/
theorem val_injective [P.IsRootSystem] : Function.Injective (val (φ := φ)) :=
  val_injective_of_rootSpan_eq_top RootPairing.IsRootSystem.span_root_eq_top

/-! ### Base-point transport -/

/-- Equality of base valuations induces an `ℝ`-affine equivalence of apartments preserving both
valuations and displacements. -/
def congr (h : φ = ψ) : Apartment φ ≃ᵃ[ℝ] Apartment ψ :=
  h ▸ AffineEquiv.refl ℝ (Apartment φ)

@[simp]
theorem congr_refl : congr (rfl : φ = φ) = AffineEquiv.refl ℝ (Apartment φ) :=
  (rfl)

@[simp]
theorem congr_val (h : φ = ψ) (x : Apartment φ) : (congr h x).val = x.val := by
  subst h
  rfl

@[simp]
theorem congr_displacement (h : φ = ψ) (x : Apartment φ) :
    (congr h x).displacement = x.displacement := by
  subst h
  rfl

@[simp]
theorem congr_base (h : φ = ψ) : congr h (base φ) = base ψ := by
  subst h
  rfl

@[simp]
theorem congr_symm (h : φ = ψ) : (congr h).symm = congr h.symm := by
  subst h
  rfl

@[simp]
theorem congr_trans (h₁ : φ = ψ) (h₂ : ψ = χ) :
    (congr h₁).trans (congr h₂) = congr (h₁.trans h₂) := by
  subst h₁ h₂
  rfl

/-- Re-centering `Apartment φ` at a point `x₀` gives an `ℝ`-affine equivalence onto
`Apartment x₀.val` sending `x₀` to `base x₀.val` and preserving the underlying valuation at every
point. -/
def transport (x₀ : Apartment φ) : Apartment φ ≃ᵃ[ℝ] Apartment x₀.val :=
  (AffineEquiv.vaddConst ℝ x₀).symm.trans (AffineEquiv.vaddConst ℝ (base x₀.val))

theorem transport_apply (x₀ x : Apartment φ) :
    x₀.transport x = (x -ᵥ x₀) +ᵥ base x₀.val :=
  (rfl)

@[simp]
theorem transport_displacement (x₀ x : Apartment φ) :
    (x₀.transport x).displacement = x.displacement - x₀.displacement := by
  simp [transport_apply, vsub_displacement]

@[simp]
theorem transport_val (x₀ x : Apartment φ) : (x₀.transport x).val = x.val := by
  rw [transport_apply, vadd_val, base_val, ← val_eq_val_shift_vsub]

@[simp]
theorem transport_self (x₀ : Apartment φ) : x₀.transport x₀ = base x₀.val := by
  ext
  simp

@[simp]
theorem linear_transport (x₀ : Apartment φ) : x₀.transport.linear = LinearEquiv.refl ℝ N := by
  ext v
  have h := x₀.transport.map_vadd x₀ v
  rw [transport_self, transport_apply, vadd_vsub] at h
  exact vadd_right_cancel (base x₀.val) h.symm

@[simp]
theorem transport_symm_displacement (x₀ : Apartment φ) (y : Apartment x₀.val) :
    (x₀.transport.symm y).displacement = y.displacement + x₀.displacement := by
  have h := x₀.transport_displacement (x₀.transport.symm y)
  rw [AffineEquiv.apply_symm_apply] at h
  exact eq_add_of_sub_eq h.symm

@[simp]
theorem transport_symm_val (x₀ : Apartment φ) (y : Apartment x₀.val) :
    (x₀.transport.symm y).val = y.val := by
  rw [← x₀.transport_val (x₀.transport.symm y), AffineEquiv.apply_symm_apply]

@[simp]
theorem transport_symm_base (x₀ : Apartment φ) : x₀.transport.symm (base x₀.val) = x₀ := by
  ext
  simp

/-- Cocycle compatibility of `transport`: re-centering at `x₀` and then at `x₀.transport x₁` agrees
with re-centering directly at `x₁`. -/
theorem transport_trans (x₀ x₁ : Apartment φ) :
    (x₀.transport.trans (x₀.transport x₁).transport).trans (congr (x₀.transport_val x₁)) =
      x₁.transport := by
  ext x : 1
  ext
  simp only [AffineEquiv.trans_apply, congr_displacement, transport_displacement]
  abel

/-- Changing the chosen base point from `y₀` to `x₀` shifts coordinates by the constant vector
`y₀ -ᵥ x₀`. When `x₀.val = y₀.val`, this shift lies in `⨅ i, ker (P.root' i)`, measuring the
central ambiguity of identifying `Apartment x₀.val` with `Apartment φ`. -/
theorem transport_displacement_sub (x₀ y₀ x : Apartment φ) :
    (x₀.transport x).displacement - (y₀.transport x).displacement = y₀ -ᵥ x₀ := by
  rw [transport_displacement, transport_displacement, vsub_displacement]
  abel

end Affine

/-! ### Pointwise root-group filtrations -/

section Filtration

variable {φ ψ : Valuation D}

/-- The filtration subgroup `U_x(a, r) ≤ D.U a` attached to a point `x : Apartment φ`, root `a`,
and threshold `r : ℝ`. -/
noncomputable def filtrationAt (x : Apartment φ) (i : ι) (r : ℝ) : Subgroup G :=
  x.val.filtration i r

theorem filtrationAt_eq_filtration (x : Apartment φ) (i : ι) (r : ℝ) :
    x.filtrationAt i r = x.val.filtration i r :=
  (rfl)

@[simp]
theorem mem_filtrationAt_iff {x : Apartment φ} {i : ι} {r : ℝ} {g : G} :
    g ∈ x.filtrationAt i r ↔ ∃ h : g ∈ D.U i, (r : WithTop ℝ) ≤ x.val i ⟨g, h⟩ :=
  x.val.mem_filtration_iff

-- Not `@[simp]`: `simp` proves it from `mem_filtrationAt_iff` and `Subtype.coe_eta`.
theorem coe_mem_filtrationAt_iff (x : Apartment φ) {i : ι} {r : ℝ} (u : D.U i) :
    (u : G) ∈ x.filtrationAt i r ↔ (r : WithTop ℝ) ≤ x.val i u :=
  x.val.coe_mem_filtration_iff u

/-- Membership of `u ∈ D.U i` in `x.filtrationAt i r` in terms of the base valuation `φ`:
`(r : WithTop ℝ) ≤ φ i u + P.root' i (x -ᵥ base φ)`. -/
theorem coe_mem_filtrationAt_iff_base (x : Apartment φ) {i : ι} {r : ℝ} (u : D.U i) :
    (u : G) ∈ x.filtrationAt i r ↔
      (r : WithTop ℝ) ≤ φ i u + (P.root' i (x -ᵥ base φ) : WithTop ℝ) := by
  rw [x.coe_mem_filtrationAt_iff, val_apply, vsub_base]

@[simp]
theorem filtrationAt_base (φ : Valuation D) (i : ι) (r : ℝ) :
    (base φ).filtrationAt i r = φ.filtration i r :=
  (rfl)

@[simp]
theorem filtrationAt_ofDisplacement (φ : Valuation D) (v : N) (i : ι) (r : ℝ) :
    (ofDisplacement φ v).filtrationAt i r = φ.filtration i (r - P.root' i v) := by
  rw [filtrationAt_eq_filtration, ofDisplacement_val, Valuation.filtration_shift]

/-- Translating a point by `v : N` shifts the filtration threshold of root `i` by `-P.root' i v`. -/
@[simp]
theorem filtrationAt_vadd (v : N) (x : Apartment φ) (i : ι) (r : ℝ) :
    (v +ᵥ x).filtrationAt i r = x.filtrationAt i (r - P.root' i v) := by
  rw [filtrationAt_eq_filtration, vadd_val, Valuation.filtration_shift, filtrationAt_eq_filtration]

theorem filtrationAt_le_U (x : Apartment φ) (i : ι) (r : ℝ) : x.filtrationAt i r ≤ D.U i :=
  x.val.filtration_le_U i r

theorem filtrationAt_antitone (x : Apartment φ) (i : ι) : Antitone (x.filtrationAt i) :=
  x.val.filtration_antitone i

@[simp]
theorem iInf_filtrationAt (x : Apartment φ) (i : ι) : (⨅ r : ℝ, x.filtrationAt i r) = ⊥ :=
  x.val.iInf_filtration i

@[simp]
theorem iSup_filtrationAt (x : Apartment φ) (i : ι) : (⨆ r : ℝ, x.filtrationAt i r) = D.U i :=
  x.val.iSup_filtration i

theorem commutator_filtrationAt_le (x : Apartment φ) {i j : ι}
    (hij : ∀ c : ℝ, 0 < c → P.root j ≠ -(c • P.root i)) (k l : ℝ) :
    ⁅x.filtrationAt i k, x.filtrationAt j l⁆ ≤
      ⨆ (n) (p : ℕ) (q : ℕ) (_ : 0 < p ∧ 0 < q ∧ P.root n = p • P.root i + q • P.root j),
        x.filtrationAt n (p * k + q * l) :=
  x.val.commutator_filtration_le hij k l

@[simp]
theorem filtrationAt_congr (h : φ = ψ) (x : Apartment φ) (i : ι) (r : ℝ) :
    (congr h x).filtrationAt i r = x.filtrationAt i r := by
  subst h
  rfl

@[simp]
theorem filtrationAt_transport (x₀ x : Apartment φ) (i : ι) (r : ℝ) :
    (x₀.transport x).filtrationAt i r = x.filtrationAt i r := by
  rw [filtrationAt_eq_filtration, transport_val, filtrationAt_eq_filtration]

@[simp]
theorem filtrationAt_transport_symm (x₀ : Apartment φ) (y : Apartment x₀.val) (i : ι) (r : ℝ) :
    (x₀.transport.symm y).filtrationAt i r = y.filtrationAt i r := by
  rw [filtrationAt_eq_filtration, transport_symm_val, filtrationAt_eq_filtration]

/-- Two points of `Apartment φ` have the same root-group filtrations at all roots and thresholds if
and only if they have the same underlying valuation. -/
theorem forall_filtrationAt_eq_iff_val_eq {x y : Apartment φ} :
    (∀ (i : ι) (r : ℝ), x.filtrationAt i r = y.filtrationAt i r) ↔ x.val = y.val :=
  Valuation.forall_filtration_eq_iff

/-- When the roots span `M` over `ℝ`, a point of `Apartment φ` is uniquely determined by its
root-group filtrations. -/
theorem forall_filtrationAt_eq_iff_eq_of_rootSpan_eq_top (hP : P.rootSpan ℝ = ⊤)
    {x y : Apartment φ} :
    (∀ (i : ι) (r : ℝ), x.filtrationAt i r = y.filtrationAt i r) ↔ x = y :=
  forall_filtrationAt_eq_iff_val_eq.trans (val_injective_of_rootSpan_eq_top hP).eq_iff

/-- For a root system (`[P.IsRootSystem]`), a point of `Apartment φ` is uniquely determined by its
root-group filtrations. -/
theorem forall_filtrationAt_eq_iff_eq [P.IsRootSystem] {x y : Apartment φ} :
    (∀ (i : ι) (r : ℝ), x.filtrationAt i r = y.filtrationAt i r) ↔ x = y :=
  forall_filtrationAt_eq_iff_eq_of_rootSpan_eq_top RootPairing.IsRootSystem.span_root_eq_top

end Filtration

end Apartment

/-! ### Compatibility of torus translations with apartment filtrations -/

namespace Valuation

variable {φ : Valuation D}

/-- If `φ` is compatible with `ν : D.T → N`, conjugation by `z ∈ D.T` carries the filtration at
`x : Apartment φ` onto the filtration at `ν z +ᵥ x`. -/
theorem IsCompatible.conj_smul_filtrationAt {ν : D.T → N} (h : φ.IsCompatible ν)
    (x : Apartment φ) (i : ι) (z : D.T) (r : ℝ) :
    ConjAct.toConjAct (z : G) • x.filtrationAt i r = (ν z +ᵥ x).filtrationAt i r := by
  have hx : x.val.IsCompatible ν := x.isCompatible_val_iff.mpr h
  rw [Apartment.filtrationAt_vadd, Apartment.filtrationAt_eq_filtration,
    Apartment.filtrationAt_eq_filtration, x.val.isCompatible_iff_filtration.mp hx i z r]

/-- `φ` is compatible with `ν : D.T → N` if and only if conjugation by `z ∈ D.T` translates the
filtrations at `Apartment.base φ` to `ν z +ᵥ Apartment.base φ`. -/
theorem isCompatible_iff_filtrationAt (φ : Valuation D) {ν : D.T → N} :
    φ.IsCompatible ν ↔ ∀ (i : ι) (z : D.T) (r : ℝ),
      ConjAct.toConjAct (z : G) • (Apartment.base φ).filtrationAt i r =
        (ν z +ᵥ Apartment.base φ).filtrationAt i r := by
  simp only [φ.isCompatible_iff_filtration, Apartment.filtrationAt_vadd,
    Apartment.filtrationAt_base]

/-- `φ` is compatible with `ν : D.T → N` if and only if conjugation by `z ∈ D.T` translates the
pointwise filtrations at every `x : Apartment φ` by `ν z`. -/
theorem isCompatible_iff_forall_filtrationAt (φ : Valuation D) {ν : D.T → N} :
    φ.IsCompatible ν ↔ ∀ (x : Apartment φ) (i : ι) (z : D.T) (r : ℝ),
      ConjAct.toConjAct (z : G) • x.filtrationAt i r = (ν z +ᵥ x).filtrationAt i r :=
  ⟨fun h x i z r ↦ h.conj_smul_filtrationAt x i z r,
    fun h ↦ (isCompatible_iff_filtrationAt φ).mpr (h (Apartment.base φ))⟩

/-- When the roots span `M` over `ℝ`, a `φ`-compatible map `D.T → N` is unique. -/
theorem IsCompatible.eq_of_rootSpan_eq_top (hP : P.rootSpan ℝ = ⊤) {ν₁ ν₂ : D.T → N}
    (h₁ : φ.IsCompatible ν₁) (h₂ : φ.IsCompatible ν₂) : ν₁ = ν₂ := by
  ext z
  exact sub_eq_zero.mp (eq_zero_of_forall_root'_eq_zero hP fun i ↦
    (h₁.iff_forall_root'_sub_eq_zero.mp h₂) i z)

/-- For a root system (`[P.IsRootSystem]`), a `φ`-compatible map `D.T → N` is unique. -/
theorem IsCompatible.eq [P.IsRootSystem] {ν₁ ν₂ : D.T → N}
    (h₁ : φ.IsCompatible ν₁) (h₂ : φ.IsCompatible ν₂) : ν₁ = ν₂ :=
  h₁.eq_of_rootSpan_eq_top RootPairing.IsRootSystem.span_root_eq_top h₂

end Valuation

/-! ### Wall reflections on the apartment -/

namespace Apartment

variable {φ : Valuation D}

/-- The affine reflection of `Apartment φ` across the affine hyperplane
`{x : Apartment φ | P.root' i (x -ᵥ base φ) + k = 0}`, obtained by transporting
`P.affineCoreflection i (-k)` along `AffineEquiv.vaddConst ℝ (base φ)`. -/
def wallReflection (φ : Valuation D) (i : ι) (k : ℝ) : Apartment φ ≃ᵃ[ℝ] Apartment φ :=
  (AffineEquiv.vaddConst ℝ (base φ)).symm.trans
    ((P.affineCoreflection i (-k)).trans (AffineEquiv.vaddConst ℝ (base φ)))

@[simp]
theorem wallReflection_displacement (φ : Valuation D) (i : ι) (k : ℝ) (x : Apartment φ) :
    (wallReflection φ i k x).displacement = P.affineCoreflection i (-k) x.displacement := by
  simp [wallReflection, vsub_base]

@[simp]
theorem wallReflection_ofDisplacement (φ : Valuation D) (i : ι) (k : ℝ) (v : N) :
    wallReflection φ i k (ofDisplacement φ v) =
      ofDisplacement φ (P.affineCoreflection i (-k) v) := by
  ext
  simp

/-- Explicit displacement formula for `wallReflection`:
`s_{a, k}(x) = -(a(x -ᵥ base φ) + k) a^∨ +ᵥ x` (Bruhat–Tits I, 6.2.7). -/
theorem wallReflection_apply (φ : Valuation D) (i : ι) (k : ℝ) (x : Apartment φ) :
    wallReflection φ i k x = -(P.root' i (x -ᵥ base φ) + k) • P.coroot i +ᵥ x := by
  ext
  rw [wallReflection_displacement, RootPairing.affineCoreflection_apply_eq_sub, vadd_displacement,
    vsub_base, sub_neg_eq_add, neg_smul, sub_eq_neg_add]

@[simp]
theorem linear_wallReflection (φ : Valuation D) (i : ι) (k : ℝ) :
    (wallReflection φ i k).linear = P.coreflection i := by
  ext v
  have h := congrArg displacement ((wallReflection φ i k).map_vadd (base φ) v)
  simp only [wallReflection_displacement, vadd_displacement, base_displacement, add_zero,
    RootPairing.affineCoreflection_apply, map_zero, zero_add] at h
  exact add_right_cancel h.symm

@[simp]
theorem wallReflection_wallReflection (φ : Valuation D) (i : ι) (k : ℝ) (x : Apartment φ) :
    wallReflection φ i k (wallReflection φ i k x) = x := by
  ext
  simp

@[simp]
theorem wallReflection_mul_self (φ : Valuation D) (i : ι) (k : ℝ) :
    wallReflection φ i k * wallReflection φ i k = 1 := by
  ext x
  simp

@[simp]
theorem inv_wallReflection (φ : Valuation D) (i : ι) (k : ℝ) :
    (wallReflection φ i k)⁻¹ = wallReflection φ i k :=
  inv_eq_of_mul_eq_one_right (wallReflection_mul_self φ i k)

@[simp]
theorem symm_wallReflection (φ : Valuation D) (i : ι) (k : ℝ) :
    (wallReflection φ i k).symm = wallReflection φ i k :=
  inv_wallReflection φ i k

/-- Two parallel wall reflections compose to a translation by a multiple of the coroot:
`s_{a, k} ∘ s_{a, l} = t_{(l - k) a^∨}`. -/
theorem wallReflection_mul_wallReflection (φ : Valuation D) (i : ι) (k l : ℝ) :
    wallReflection φ i k * wallReflection φ i l =
      AffineEquiv.constVAdd ℝ (Apartment φ) ((l - k) • P.coroot i) := by
  ext x
  have h := congrFun
    (congrArg DFunLike.coe (P.affineCoreflection_mul_affineCoreflection i (-k) (-l)))
    x.displacement
  simp only [AffineEquiv.coe_mul, Function.comp_apply, wallReflection_displacement,
    AffineEquiv.constVAdd_apply, vadd_displacement] at h ⊢
  rw [h, vadd_eq_add, neg_sub_neg]

theorem wallReflection_vsub_self (φ : Valuation D) (i : ι) (k : ℝ) (x : Apartment φ) :
    wallReflection φ i k x -ᵥ x = -(P.root' i (x -ᵥ base φ) + k) • P.coroot i := by
  rw [wallReflection_apply, vadd_vsub]

theorem wallReflection_vsub_mem_corootSpan (φ : Valuation D) (i : ι) (k : ℝ) (x : Apartment φ) :
    wallReflection φ i k x -ᵥ x ∈ P.corootSpan ℝ := by
  rw [wallReflection_vsub_self]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- The fixed-point set of `wallReflection φ i k` is the hyperplane
`{x | P.root' i (x -ᵥ base φ) + k = 0}`. -/
@[simp]
theorem wallReflection_apply_eq_self_iff {i : ι} {k : ℝ} {x : Apartment φ} :
    wallReflection φ i k x = x ↔ P.root' i (x -ᵥ base φ) + k = 0 := by
  rw [← displacement_inj, wallReflection_displacement,
    RootPairing.affineCoreflection_apply_eq_self_iff, vsub_base, add_eq_zero_iff_eq_neg]

theorem wallReflection_apply_of_add_eq_zero {i : ι} {k : ℝ} {x : Apartment φ}
    (h : P.root' i (x -ᵥ base φ) + k = 0) : wallReflection φ i k x = x :=
  wallReflection_apply_eq_self_iff.mpr h

theorem root'_wallReflection_vsub_base (φ : Valuation D) (i j : ι) (k : ℝ) (x : Apartment φ) :
    P.root' j (wallReflection φ i k x -ᵥ base φ) =
      P.root' (P.reflectionPerm i j) (x -ᵥ base φ) - P.pairing j i * k := by
  rw [vsub_base, wallReflection_displacement, P.root'_affineCoreflection i j (-k), vsub_base,
    mul_neg, ← sub_eq_add_neg]

theorem root'_self_wallReflection_vsub_base (φ : Valuation D) (i : ι) (k : ℝ) (x : Apartment φ) :
    P.root' i (wallReflection φ i k x -ᵥ base φ) = -(P.root' i (x -ᵥ base φ) + 2 * k) := by
  rw [vsub_base, wallReflection_displacement, P.root'_affineCoreflection_self, vsub_base]
  ring

/-- Base-point invariance of wall reflections: re-centering `Apartment φ` at `x₀` conjugates
`wallReflection φ i k` to `wallReflection x₀.val i (k + P.root' i (x₀ -ᵥ base φ))`. When
`φ i u = k`, the shifted constant `k + P.root' i (x₀ -ᵥ base φ)` is `x₀.val i u`, so the wall
reflection attached to `u ∈ D.U i \ {1}` does not depend on the choice of base valuation. -/
theorem transport_wallReflection (x₀ : Apartment φ) (i : ι) (k : ℝ) (x : Apartment φ) :
    x₀.transport (wallReflection φ i k x) =
      wallReflection x₀.val i (k + P.root' i (x₀ -ᵥ base φ)) (x₀.transport x) := by
  ext
  simp only [transport_displacement, wallReflection_displacement,
    RootPairing.affineCoreflection_apply_eq_sub, vsub_base, map_sub]
  module

/-- Rank-one compatibility of `wallReflection` with conjugation by `m = u' u u'' ∈ M a` where
`φ a u = k` (Bruhat–Tits I, 6.2.7): conjugation by `m` carries `U_x(-a, r)` onto
`U_{s_{a, k}(x)}(a, r)`. -/
theorem conj_smul_filtrationAt_reflectionPerm {i : ι} {k : ℝ} {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)} (hm : (u' : G) * u * u'' ∈ D.reflectionCoset i)
    (hu : φ i u = k) (x : Apartment φ) (r : ℝ) :
    ConjAct.toConjAct ((u' : G) * u * u'') • x.filtrationAt (P.reflectionPerm i i) r =
      (wallReflection φ i k x).filtrationAt i r := by
  rw [← x.ofDisplacement_displacement_self, filtrationAt_ofDisplacement,
    P.root'_reflectionPerm_self, LinearMap.neg_apply, sub_neg_eq_add,
    φ.conj_smul_filtration_reflectionPerm hm hu, wallReflection_ofDisplacement,
    filtrationAt_ofDisplacement, P.root'_affineCoreflection_self]
  congr 1
  ring

/-- Symmetric form of `conj_smul_filtrationAt_reflectionPerm`: for `m = u' u u'' ∈ M a`
with `φ a u = k`, conjugation by `m` carries `U_x(a, r)` onto `U_{s_{a, k}(x)}(-a, r)`. -/
theorem conj_smul_filtrationAt_eq_wallReflection_reflectionPerm {i : ι} {k : ℝ} {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)} (hm : (u' : G) * u * u'' ∈ D.reflectionCoset i)
    (hu : φ i u = k) (x : Apartment φ) (r : ℝ) :
    ConjAct.toConjAct ((u' : G) * u * u'') • x.filtrationAt i r =
      (wallReflection φ i k x).filtrationAt (P.reflectionPerm i i) r := by
  rw [← x.ofDisplacement_displacement_self, filtrationAt_ofDisplacement,
    φ.conj_smul_filtration_eq_filtration_reflectionPerm hm hu, wallReflection_ofDisplacement,
    filtrationAt_ofDisplacement, P.root'_reflectionPerm_self, LinearMap.neg_apply,
    P.root'_affineCoreflection_self]
  congr 1
  ring

end Apartment

end TauCeti.BruhatTits
