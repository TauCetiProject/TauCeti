/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.Algebra.GroupAction.CrossedHom
public import TauCeti.Algebra.GroupAction.TypeTags

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Identities of cocycles

Facts about cocycles in the sense of Mathlib's unbundled `groupCohomology.IsCocycle₁`,
`groupCohomology.IsCocycle₂` and `groupCohomology.IsMulCocycle₁`, which need no topology and no
representation:

* `groupCohomology.smul_apply_inv_mul_mul_of_isCocycle₁`: conjugating the argument by `k` and
  then acting by `k` adds `m • f k - f k` to the value at `m`, for any scalar multiplication of
  `G` on `M`: `k • f (k⁻¹ * m * k) = m • f k - f k + f m`.
* `groupCohomology.smul_zero_of_isCocycle₁`: an action admitting a `1`-cocycle fixes `0`.
* `groupCohomology.isMulCocycle₁_iff_isMulCrossedHom`, `groupCohomology.IsMulCocycle₁.pow`:
  over a commutative coefficient group, `IsMulCocycle₁` agrees with `TauCeti.IsMulCrossedHom` and
  is closed under pointwise powers.
* `groupCohomology.IsCocycle₁.add` and `groupCohomology.IsCoboundary₁.isCocycle₁`: `1`-cocycles
  are closed under addition, and `1`-coboundaries are `1`-cocycles, for a distributive action.
* `groupCohomology.zeroLocus`: the zero locus `{g | f g = 0}` is a subgroup of `G`, for any group
  action (not necessarily distributive) admitting the cocycle. As a set it is `f ⁻¹' {0}`
  (`groupCohomology.coe_zeroLocus`), and for distributive actions it agrees with `oneLocus` via
  `Additive.toMul` (`groupCohomology.zeroLocus_eq_oneLocus`) and `Multiplicative.ofAdd`
  (`groupCohomology.zeroLocus_eq_oneLocus_ofAdd`). `GroupCohomology/Cocycle/Topology.lean` shows it
  is closed when `f` is continuous into a `T1` space, and deduces that such an `f` vanishing on a
  topological generating set vanishes everywhere.
* `groupCohomology.IsCocycle₁.conj`: for a `G`-module `M`, a `1`-cocycle `c` on a subgroup `H`
  conjugates to the `1`-cocycle `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`, and its zero locus is
  conjugated by `g` (`groupCohomology.map_subtype_zeroLocus_conj`).

* `TauCeti.isCocycle₁_ext_of_forall_mem_zpowers`: a one-cocycle on a cyclic group is
  determined by its value at a generator.
* `TauCeti.isCocycle₂_ext_of_forall_mem_zpowers`: a two-cocycle on a cyclic group is
  determined by its values with the generator as second argument.
* `TauCeti.sum_smul_apply_eq_zero_of_isCocycle₁`: on a finite group, the group norm kills
  every value of a one-cocycle.

For the bundled one-cocycles `groupCohomology.cocycles₁ A` of a representation `A`:

* `groupCohomology.cocycles₁_map_mul` and `groupCohomology.cocycles₁_apply_inv`: the cocycle
  identity `f (g * h) = ρ g (f h) + f g` and the inverse formula `f g⁻¹ = -ρ g⁻¹ (f g)`.
* `groupCohomology.cocycles₁_ext_of_closure_eq_top`: a one-cocycle is determined by its values
  on a generating set; `groupCohomology.cocycles₁_list_prod_eq_zero`: it vanishes on a product of
  elements at which it vanishes. Hence `Z¹(G, A)` is a finite module when `G` is finitely
  generated and `A` is a finite module over a Noetherian ring (an instance).
* `groupCohomology.cocycles₁_apply_inv_mul_inv_mul_mul`: the value of a one-cocycle at a
  commutator `a⁻¹ b⁻¹ a b`, given by the Fox derivatives of the commutator.
* `groupCohomology.cocycles₁_apply_mem_coinvariantsKer_of_mem_commutator`: modulo the coinvariant
  kernel a one-cocycle is a homomorphism, so it takes values in the coinvariant kernel on the
  commutator subgroup.

Continuous cohomology uses the conjugation identity in the five-term sequence and in
transgression, and the cyclic-group facts in its first and second cohomology computations.
-/

public section

universe u w

namespace groupCohomology

/-- Conjugating the argument of a `1`-cocycle by `k` and then acting by `k` adds `m • c k - c k`
to its value at `m`: `k • c (k⁻¹ * m * k) = m • c k - c k + c m`. Only a scalar multiplication
of `G` on `M` is needed, not an action. -/
theorem smul_apply_inv_mul_mul_of_isCocycle₁ {G M : Type*} [Group G] [AddCommGroup M] [SMul G M]
    {c : G → M} (hc : IsCocycle₁ c) (k m : G) :
    k • c (k⁻¹ * m * k) = m • c k - c k + c m := by
  have hmul : k * (k⁻¹ * m * k) = m * k := by group
  have h := hc k (k⁻¹ * m * k)
  rw [hmul, hc m k] at h
  rw [eq_sub_of_add_eq h.symm]
  abel

/-- A monoid action on an additive group that admits a `1`-cocycle fixes `0`. -/
theorem smul_zero_of_isCocycle₁ {G M : Type*} [Monoid G] [AddCommGroup M] [MulAction G M]
    {f : G → M} (hf : IsCocycle₁ f) (g : G) : g • (0 : M) = 0 := by
  simpa only [mul_one, map_one_of_isCocycle₁ hf, right_eq_add] using hf g 1

/-- Over a commutative coefficient group, `groupCohomology.IsMulCocycle₁` is
`TauCeti.IsMulCrossedHom`. -/
theorem isMulCocycle₁_iff_isMulCrossedHom {G M : Type*} [Mul G] [CommGroup M] [SMul G M]
    {f : G → M} : IsMulCocycle₁ f ↔ TauCeti.IsMulCrossedHom f :=
  TauCeti.isMulCrossedHom_iff.symm

/-- A pointwise power of a multiplicative `1`-cocycle is a multiplicative `1`-cocycle. -/
theorem IsMulCocycle₁.pow {G M : Type*} [Monoid G] [CommGroup M] [MulDistribMulAction G M]
    {f : G → M} (hf : IsMulCocycle₁ f) (n : ℕ) : IsMulCocycle₁ (f ^ n) := fun g h => by
  simp only [Pi.pow_apply, hf g h, mul_pow, smul_pow']

/-- An additive `1`-cocycle into `Additive M`, read multiplicatively via `Additive.toMul`, is a
multiplicative crossed homomorphism. -/
theorem IsCocycle₁.isMulCrossedHom_toMul {G M : Type*} [Monoid G] [CommGroup M]
    [MulDistribMulAction G M] {f : G → Additive M} (hf : IsCocycle₁ f) :
    TauCeti.IsMulCrossedHom (fun g => (f g).toMul) :=
  TauCeti.isMulCrossedHom_iff.mpr fun g h => by
    simpa only [toMul_add, Additive.toMul_smul] using congrArg Additive.toMul (hf g h)

/-- An additive `1`-cocycle, read multiplicatively in `Multiplicative M` via
`Multiplicative.ofAdd`, is a multiplicative crossed homomorphism. -/
theorem IsCocycle₁.isMulCrossedHom_ofAdd {G M : Type*} [Monoid G] [AddCommGroup M]
    [DistribMulAction G M] {f : G → M} (hf : IsCocycle₁ f) :
    TauCeti.IsMulCrossedHom (fun g => Multiplicative.ofAdd (f g)) :=
  TauCeti.isMulCrossedHom_iff.mpr fun g h => by
    simpa only [ofAdd_add, Multiplicative.ofAdd_smul] using congrArg Multiplicative.ofAdd (hf g h)

/-- The sum of two `1`-cocycles is a `1`-cocycle. -/
theorem IsCocycle₁.add {G M : Type*} [Mul G] [AddCommGroup M] [DistribSMul G M] {f f' : G → M}
    (hf : IsCocycle₁ f) (hf' : IsCocycle₁ f') : IsCocycle₁ (f + f') := fun g h => by
  simp only [Pi.add_apply, hf g h, hf' g h, smul_add]
  abel

/-- A `1`-coboundary `g ↦ g • x - x` is a `1`-cocycle. -/
theorem IsCoboundary₁.isCocycle₁ {G M : Type*} [Monoid G] [AddCommGroup M]
    [DistribMulAction G M] {f : G → M} (hf : IsCoboundary₁ f) : IsCocycle₁ f := by
  obtain ⟨x, hx⟩ := hf
  intro g h
  rw [← hx, ← hx, ← hx, smul_sub, mul_smul]
  abel

section ZeroLocus

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M]

/-- **The zero locus of a `1`-cocycle**, `{g | f g = 0}`, as a subgroup of `G`, for any group
action (not necessarily distributive). -/
def zeroLocus {f : G → M} (hf : IsCocycle₁ f) : Subgroup G where
  carrier := {g | f g = 0}
  one_mem' := map_one_of_isCocycle₁ hf
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [hf g h, hg, hh, smul_zero_of_isCocycle₁ hf, add_zero]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := map_inv_of_isCocycle₁ hf g
    rwa [hg, neg_zero, ← smul_zero_of_isCocycle₁ hf g, smul_left_cancel_iff] at h

/-- An element lies in the zero locus of a `1`-cocycle exactly when the cocycle vanishes there. -/
@[simp]
theorem mem_zeroLocus {f : G → M} (hf : IsCocycle₁ f) {g : G} : g ∈ zeroLocus hf ↔ f g = 0 :=
  Iff.rfl

/-- The zero locus of a `1`-cocycle is the preimage of `0`. -/
@[simp]
theorem coe_zeroLocus {f : G → M} (hf : IsCocycle₁ f) : (zeroLocus hf : Set G) = f ⁻¹' {0} :=
  (rfl)

end ZeroLocus

/-- On `Additive N`, the zero locus of an additive `1`-cocycle agrees with the `1`-locus of its
multiplicative form. -/
theorem zeroLocus_eq_oneLocus {G N : Type*} [Group G] [CommGroup N] [MulDistribMulAction G N]
    {f : G → Additive N} (hf : IsCocycle₁ f) :
    zeroLocus hf = hf.isMulCrossedHom_toMul.oneLocus := by
  ext g
  simp

/-- For a distributive action, the zero locus of an additive `1`-cocycle agrees with the `1`-locus
of its multiplicative form in `Multiplicative M`. -/
theorem zeroLocus_eq_oneLocus_ofAdd {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    {f : G → M} (hf : IsCocycle₁ f) :
    zeroLocus hf = hf.isMulCrossedHom_ofAdd.oneLocus := by
  ext g
  simp

section Conj

open scoped Pointwise

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M] {H : Subgroup G}

/-- Conjugating a `1`-cocycle `c` on a subgroup `H` by `g` gives a `1`-cocycle on `g H g⁻¹`,
namely `x ↦ g • c (g⁻¹ * x * g)`; the subgroups act on `M` by restriction. -/
theorem IsCocycle₁.conj {c : H → M} (hc : IsCocycle₁ c) (g : G) :
    IsCocycle₁ fun x : ↥(MulAut.conj g • H) =>
      g • c ((Subgroup.equivSMul (MulAut.conj g) H).symm x) := fun x y => by
  simpa only [toAdd_mul, Multiplicative.toAdd_smul, toAdd_ofAdd] using
    congrArg Multiplicative.toAdd ((hc.isMulCrossedHom_ofAdd.conj g).map_mul x y)

/-- The zero locus of the conjugate `x ↦ g • c (g⁻¹ * x * g)` of a `1`-cocycle on `H`, viewed
in `G`, is the conjugate by `g` of the zero locus of `c`. -/
@[simp]
theorem map_subtype_zeroLocus_conj {c : H → M} (hc : IsCocycle₁ c) (g : G) :
    (zeroLocus (hc.conj g)).map (MulAut.conj g • H).subtype =
      MulAut.conj g • (zeroLocus hc).map H.subtype := by
  rw [zeroLocus_eq_oneLocus_ofAdd, zeroLocus_eq_oneLocus_ofAdd]
  exact hc.isMulCrossedHom_ofAdd.map_subtype_oneLocus_conj g

end Conj

/-! ### One-cocycles of a representation -/

section Rep

variable {k G : Type u} [CommRing k] [Group G] {A : Rep.{w} k G}

/-- The cocycle identity `f (g * h) = ρ g (f h) + f g` of a one-cocycle of a representation. -/
theorem cocycles₁_map_mul (f : cocycles₁ A) (g h : G) : f (g * h) = A.ρ g (f h) + f g :=
  (mem_cocycles₁_iff (f : G → A)).1 f.property g h

/-- The value of a one-cocycle at an inverse, `f g⁻¹ = -ρ g⁻¹ (f g)`. -/
theorem cocycles₁_apply_inv (f : cocycles₁ A) (g : G) : f g⁻¹ = -A.ρ g⁻¹ (f g) := by
  rw [← map_neg, ← cocycles₁_map_inv f g, Representation.inv_self_apply]

/-- **A one-cocycle is determined by its values on a generating set.** -/
theorem cocycles₁_ext_of_closure_eq_top {s : Set G} (hs : Subgroup.closure s = ⊤)
    {f f' : cocycles₁ A} (h : ∀ g ∈ s, f g = f' g) : f = f' := by
  ext g
  induction hs.ge (Subgroup.mem_top g) using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => simp
  | mul g g' _ _ hg hg' => rw [cocycles₁_map_mul, cocycles₁_map_mul f', hg, hg']
  | inv g _ hg => rw [cocycles₁_apply_inv, cocycles₁_apply_inv f', hg]

/-- **The one-cocycles of a finitely generated group are finite.** For a finite module `A` over
a Noetherian ring, evaluation on a finite generating set `S` embeds `Z¹(G, A)` into `S → A`. -/
instance [IsNoetherianRing k] [Group.FG G] [Module.Finite k A] : Module.Finite k (cocycles₁ A) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.1 ‹Group.FG G›
  have := hfin.to_subtype
  let ev : cocycles₁ A →ₗ[k] (S → A) :=
    { toFun f x := f x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact Module.Finite.of_injective ev fun f f' h ↦
    cocycles₁_ext_of_closure_eq_top hS fun g hg ↦ congrFun h ⟨g, hg⟩

/-- A one-cocycle vanishing at every element of a list vanishes at its product. -/
theorem cocycles₁_list_prod_eq_zero (f : cocycles₁ A) {l : List G} (hl : ∀ x ∈ l, f x = 0) :
    f l.prod = 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, cocycles₁_map_mul, ih fun y hy ↦ hl y (List.mem_cons_of_mem x hy),
      hl x List.mem_cons_self, map_zero, add_zero]

/-- **The value of a one-cocycle at a commutator.** For the commutator `a⁻¹ * b⁻¹ * a * b`, the
cocycle identity gives
`f (a⁻¹ b⁻¹ a b) = (ρ (a⁻¹ b⁻¹) - ρ a⁻¹) (f a) + (ρ (a⁻¹ b⁻¹ a) - ρ (a⁻¹ b⁻¹)) (f b)`, the Fox
derivatives of the commutator applied to the values at `a` and `b`. -/
theorem cocycles₁_apply_inv_mul_inv_mul_mul (f : cocycles₁ A) (a b : G) :
    f (a⁻¹ * b⁻¹ * a * b) = A.ρ (a⁻¹ * b⁻¹) (f a) - A.ρ a⁻¹ (f a) +
      (A.ρ (a⁻¹ * b⁻¹ * a) (f b) - A.ρ (a⁻¹ * b⁻¹) (f b)) := by
  rw [cocycles₁_map_mul, cocycles₁_map_mul, cocycles₁_map_mul, cocycles₁_apply_inv f a,
    cocycles₁_apply_inv f b]
  simp only [map_neg, map_mul, mul_apply_eq_comp]
  abel

/-- **A one-cocycle takes values in the coinvariant kernel on the commutator subgroup.** Modulo
the coinvariant kernel the cocycle identity reads `f (g * h) = f h + f g`, so `f` becomes a
homomorphism to an abelian group, which kills commutators. -/
theorem cocycles₁_apply_mem_coinvariantsKer_of_mem_commutator (f : cocycles₁ A) {g : G}
    (hg : g ∈ commutator G) : f g ∈ Representation.Coinvariants.ker A.ρ := by
  let φ : G →* Multiplicative (Representation.Coinvariants A.ρ) :=
    { toFun g := .ofAdd (Representation.Coinvariants.mk A.ρ (f g))
      map_one' := by simp
      map_mul' g h := by
        rw [cocycles₁_map_mul]
        simp [← ofAdd_add, add_comm] }
  have hle : commutator G ≤ φ.ker := Group.Abelianization.commutator_le_ker φ
  have := hle hg
  rw [MonoidHom.mem_ker] at this
  exact (Representation.Coinvariants.mk_eq_zero _).1 (by simpa [φ] using this)

end Rep

end groupCohomology

namespace TauCeti

open groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M]

/-- Two one-cocycles on a cyclic group agree if they agree at a generator. No finiteness or
continuity hypothesis is needed, and the action need not be distributive. -/
theorem isCocycle₁_ext_of_forall_mem_zpowers {f f' : G → M} (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hf : IsCocycle₁ f) (hf' : IsCocycle₁ f')
    (h : f g = f' g) : f = f' := by
  let S : Subgroup G :=
    { carrier := {x | f x = f' x}
      one_mem' := (map_one_of_isCocycle₁ hf).trans (map_one_of_isCocycle₁ hf').symm
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [hf x y, hf' x y, hx, hy]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [← smul_left_cancel_iff x]
        rw [map_inv_of_isCocycle₁ hf, map_inv_of_isCocycle₁ hf', hx] }
  have hle : Subgroup.zpowers g ≤ S := Subgroup.zpowers_le.mpr h
  funext x
  exact hle (hg x)

/-- Two `2`-cocycles on a cyclic group agree if they agree whenever the second argument is a
generator. No finiteness or continuity hypothesis is needed, and the action need not be
distributive. -/
theorem isCocycle₂_ext_of_forall_mem_zpowers {f f' : G × G → M} (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hf : IsCocycle₂ f) (hf' : IsCocycle₂ f')
    (h : ∀ x : G, f (x, g) = f' (x, g)) : f = f' := by
  have h11 : f (1, 1) = f' (1, 1) := by
    rw [← map_one_fst_of_isCocycle₂ hf g, ← map_one_fst_of_isCocycle₂ hf' g]
    exact h 1
  have hone (x : G) : f (x, 1) = f' (x, 1) := by
    rw [map_one_snd_of_isCocycle₂ hf, map_one_snd_of_isCocycle₂ hf', h11]
  let S : Subgroup G :=
    { carrier := {y | ∀ x : G, f (x, y) = f' (x, y)}
      one_mem' := hone
      mul_mem' := by
        intro y z hy hz x
        have hmul := hf x y z
        rw [hz (x * y), hy x, hz y] at hmul
        exact add_left_cancel (hmul.symm.trans (hf' x y z))
      inv_mem' := by
        intro y hy x
        have hinv := hf x y⁻¹ y
        have hinv' := hf' x y⁻¹ y
        rw [inv_mul_cancel] at hinv hinv'
        rw [hy (x * y⁻¹), hy y⁻¹, hone x] at hinv
        exact add_left_cancel (hinv.trans hinv'.symm) }
  have hle : Subgroup.zpowers g ≤ S := Subgroup.zpowers_le.mpr h
  funext ⟨x, y⟩
  exact hle (hg y) x

omit [MulAction G M] in
/-- The value of a one-cocycle on a finite group lies in the kernel of the group norm.
This holds at every group element, not just at a cyclic generator. Even associativity and
distributivity of the scalar multiplication are unnecessary for this identity. -/
theorem sum_smul_apply_eq_zero_of_isCocycle₁ [SMul G M] [Fintype G] {f : G → M}
    (g : G) (hf : IsCocycle₁ f) : ∑ x : G, x • f g = 0 := by
  have hsum : (∑ x : G, f x) = (∑ x : G, x • f g) + ∑ x : G, f x := by
    calc
      (∑ x : G, f x) = ∑ x : G, f (x * g) :=
        (Fintype.sum_bijective _ (Group.mulRight_bijective g) _ _ (fun _ ↦ rfl)).symm
      _ = _ := by simp only [hf _ _, Finset.sum_add_distrib]
  exact (add_right_cancel (hsum.symm.trans (zero_add _).symm))

end TauCeti
