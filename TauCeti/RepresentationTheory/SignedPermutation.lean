/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import Mathlib.Tactic.Group

/-!
# Invariants of signed permutation representations

Let a group `G` act on a type `X`, and let `M` be a module over a commutative ring `R`. A
*sign cocycle* is a function `ε : G → X → ℤˣ` with

`ε (g * h) x = ε g (h • x) * ε h x`.

It defines the *signed permutation representation* `TauCeti.signedPermRep R M ε hε` of `G` on the
finitely supported functions `X →₀ M`, in which `g` sends `m` at `x` to `ε g x • m` at `g • x`
(`TauCeti.signedPermRep_single`). For `ε = 1` this is the permutation representation with
coefficients in `M`. The motivating example is a module of singular chains with coefficients in a
rank-one local system of signs, such as an orientation line: `G` permutes the simplices, and moving
a simplex transports its coefficient by a sign.

A function `f` is invariant exactly when `f (g • x) = ε g x • f x` for all `g` and `x`
(`TauCeti.mem_invariants_signedPermRep_iff`). In particular its value at `x` is fixed by the sign
`ε g x` of every element `g` of the stabilizer of `x`: it lies in the submodule
`TauCeti.signFixed R ε x` (`TauCeti.apply_mem_signFixed_of_mem_invariants`). On the stabilizer,
`ε (·) x` is a character with values `±1`, so this submodule is the invariants of a rank-one sign
representation of the stabilizer on `M`. It is all of `M` when the character is trivial
(`TauCeti.signFixed_eq_top`), and zero when the character is nontrivial and `2` is a nonzerodivisor
on `M` (`TauCeti.signFixed_eq_bot`), for instance when `2` is invertible in `R`. Without that
hypothesis it need not vanish: over `𝔽₂` the sign `-1` acts trivially, and over `ℤ/4` the vectors
fixed by `-1` are the `2`-torsion.

**The orbit decomposition.** When every orbit is finite, an invariant function is determined by
its values at a chosen representative of each orbit, and these values can be prescribed freely in
the submodules `signFixed R ε x`. This gives a linear equivalence
(`TauCeti.invariantsSignedPermRepEquiv`) between the invariants and the finitely supported
functions on the orbit space `MulAction.orbitRel.Quotient G X` whose value at an orbit `ω` lies in
`signFixed R ε ω.out`. The value of the invariant function at `a • ω.out` is `ε a ω.out` times
its value at `ω.out`, which does not depend on the choice of `a`
(`TauCeti.smul_eq_smul_of_mem_signFixed`). The set `X` may be infinite, as the set of singular
simplices of a space is; only the orbits have to be finite, as they are for a finite group
(`Finite.finite_mulAction_orbit`).

When `2` is a nonzerodivisor on `M`, each orbit therefore contributes a copy of `M` if the sign
character of the stabilizer of one, equivalently every, point of the orbit is trivial
(`TauCeti.forall_smul_eq_imp_eq_one_smul_iff`), and nothing otherwise. The invariants are then
the finitely supported functions with values in `M` on the set `TauCeti.trivialSignOrbits ε` of
orbits with trivial stabilizer sign (`TauCeti.invariantsSignedPermRepEquivFinsupp`), and the
orbit of `x` belongs to this set exactly when the stabilizer sign at `x` is trivial
(`TauCeti.mk_mem_trivialSignOrbits_iff`). For `M = R` the invariants are thus free on these
orbits, with basis the orbit vectors: the orbit basis of invariant chains with sign coefficients.
For example, `ℤ/2` acting on `ℚ` by `-1` at a single point has no nonzero invariants, while the
same group exchanging two points with sign coefficients has invariants `ℚ`, spanned by the orbit
vector with value `1` at one point and `±1` at the other.

## Main definitions

* `TauCeti.signedPermRep`: the signed permutation representation of a sign cocycle.
* `TauCeti.signFixed`: the vectors of `M` fixed by the stabilizer sign at a point.
* `TauCeti.orbitSignFixed`: the finitely supported functions on the orbit space with values in the
  stabilizer-sign-fixed vectors at the orbit representatives.
* `TauCeti.invariantsSignedPermRepEquiv`: invariants as such functions on the orbit space.
* `TauCeti.trivialSignOrbits`: the orbits with trivial stabilizer sign.
* `TauCeti.invariantsSignedPermRepEquivFinsupp`: invariants as finitely supported functions with
  values in `M` on the orbits with trivial stabilizer sign, when `2` is a nonzerodivisor on `M`.

## Main results

* `TauCeti.signedPermRep_apply_smul`: the action reads `(g • f) (g • x) = ε g x • f x`.
* `TauCeti.mem_invariants_signedPermRep_iff`: the invariance condition on coefficients.
* `TauCeti.signFixed_eq_top`, `TauCeti.signFixed_eq_bot`: the stabilizer-sign-fixed vectors are
  everything for a trivial sign and nothing for a nontrivial sign, when `2` is a nonzerodivisor.
* `TauCeti.smul_eq_smul_of_mem_signFixed`: the value `ε a x • m` at `a • x` is well defined.
* `TauCeti.orbitSignFixed_eq_supported`: when `2` is a nonzerodivisor, the orbit coefficients are
  the functions supported on the orbits with trivial stabilizer sign.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. **20** (2016), 779–1034, arXiv:1309.2370, where the
  virtual cochain complexes are invariants of relative singular chains with coefficients in an
  orientation line under a finite group.
-/

public section

namespace TauCeti

open Finsupp _root_.MulAction

variable {G X : Type*}

/-! ### The signed permutation representation -/

section Monoid

variable [Monoid G] [MulAction G X] {ε : G → X → ℤˣ}

/-- A sign cocycle takes the value `1` at the identity. -/
theorem sign_one_of_cocycle (hε : ∀ g h x, ε (g * h) x = ε g (h • x) * ε h x) (x : X) :
    ε 1 x = 1 := by
  simpa using hε 1 1 x

variable (R M : Type*) [CommSemiring R] [AddCommGroup M] [Module R M]

/-- The **signed permutation representation** of a sign cocycle `ε`: the element `g` sends the
coefficient `m` at `x` to the coefficient `ε g x • m` at `g • x`. -/
noncomputable def signedPermRep (ε : G → X → ℤˣ)
    (hε : ∀ g h x, ε (g * h) x = ε g (h • x) * ε h x) : Representation R G (X →₀ M) where
  toFun g := Finsupp.lsum R fun x ↦ Finsupp.lsingle (g • x) ∘ₗ ((ε g x : ℤ) • LinearMap.id)
  map_one' := Finsupp.lhom_ext fun x m ↦ by simp [sign_one_of_cocycle hε]
  map_mul' g h := Finsupp.lhom_ext fun x m ↦ by simp [hε, mul_smul]

variable {R M}

@[simp]
theorem signedPermRep_single (hε : ∀ g h x, ε (g * h) x = ε g (h • x) * ε h x) (g : G) (x : X)
    (m : M) : signedPermRep R M ε hε g (single x m) = single (g • x) (ε g x • m) := by
  simp [signedPermRep, Units.smul_def]

end Monoid

/-! ### The vectors fixed by the stabilizer sign -/

section SignFixed

variable [Monoid G] [MulAction G X] {ε : G → X → ℤˣ}
  (R : Type*) {M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]

/-- The vectors `m` of `M` with `ε g x • m = m` for every `g` in the stabilizer of `x`: the
invariants of the stabilizer of `x` acting on `M` through the sign `ε (·) x`. -/
def signFixed (ε : G → X → ℤˣ) (x : X) : Submodule R M where
  carrier := {m | ∀ g : G, g • x = x → ε g x • m = m}
  add_mem' ha hb g hg := by rw [smul_add, ha g hg, hb g hg]
  zero_mem' _ _ := smul_zero _
  smul_mem' r _ hm g hg := by rw [smul_comm, hm g hg]

variable {R}

@[simp]
theorem mem_signFixed_iff {x : X} {m : M} :
    m ∈ signFixed R ε x ↔ ∀ g : G, g • x = x → ε g x • m = m :=
  Iff.rfl

/-- If the sign of every element of the stabilizer of `x` is `1`, every vector is fixed. -/
theorem signFixed_eq_top {x : X} (h : ∀ g : G, g • x = x → ε g x = 1) :
    signFixed R ε x = (⊤ : Submodule R M) :=
  eq_top_iff.2 fun _ _ ↦ mem_signFixed_iff.2 fun g hg ↦ by rw [h g hg, one_smul]

/-- If some element of the stabilizer of `x` has sign `-1` and `2` is a nonzerodivisor on `M`, no
nonzero vector is fixed: a fixed vector `m` has `-m = m`. -/
theorem signFixed_eq_bot (h2 : IsSMulRegular M (2 : R)) {x : X}
    (h : ∃ g : G, g • x = x ∧ ε g x ≠ 1) : signFixed R ε x = (⊥ : Submodule R M) := by
  obtain ⟨g, hg, hne⟩ := h
  refine eq_bot_iff.2 fun m hm ↦ (Submodule.mem_bot R).2 <|
    isSMulRegular_iff_right_eq_zero_of_smul.1 h2 m ?_
  have hneg : -m = m := by
    have hfix := mem_signFixed_iff.1 hm g hg
    rwa [(Int.units_eq_one_or _).resolve_left hne, Units.neg_smul, one_smul] at hfix
  rw [two_smul]
  exact neg_eq_iff_add_eq_zero.1 hneg

end SignFixed

section Group

variable [Group G] [MulAction G X] {ε : G → X → ℤˣ}
  {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (hε : ∀ g h x, ε (g * h) x = ε g (h • x) * ε h x)

include hε

/-- The coefficient of `g • f` at `g • x` is `ε g x` times the coefficient of `f` at `x`. -/
@[simp]
theorem signedPermRep_apply_smul (g : G) (f : X →₀ M) (x : X) :
    signedPermRep R M ε hε g f (g • x) = ε g x • f x := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [hf, hf', smul_add]
  | single y m =>
    rw [signedPermRep_single]
    obtain rfl | h := eq_or_ne y x
    · simp
    · simp [h]

/-- The coefficient of `g • f` at `y` is `ε g (g⁻¹ • y)` times the coefficient of `f` at
`g⁻¹ • y`. -/
theorem signedPermRep_apply (g : G) (f : X →₀ M) (y : X) :
    signedPermRep R M ε hε g f y = ε g (g⁻¹ • y) • f (g⁻¹ • y) := by
  conv_lhs => rw [← smul_inv_smul g y]
  exact signedPermRep_apply_smul hε g f _

/-- A function is invariant under the signed permutation representation exactly when its
coefficients satisfy `f (g • x) = ε g x • f x`. -/
theorem mem_invariants_signedPermRep_iff {f : X →₀ M} :
    f ∈ (signedPermRep R M ε hε).invariants ↔ ∀ (g : G) (x : X), f (g • x) = ε g x • f x := by
  refine ⟨fun hf g x ↦ ?_, fun hf g ↦ ?_⟩
  · rw [← signedPermRep_apply_smul (R := R) hε, hf g]
  · ext y
    rw [signedPermRep_apply, ← hf, smul_inv_smul]

/-- The value of an invariant function at `x` is fixed by the stabilizer sign at `x`. -/
theorem apply_mem_signFixed_of_mem_invariants {f : X →₀ M}
    (hf : f ∈ (signedPermRep R M ε hε).invariants) (x : X) : f x ∈ signFixed R ε x :=
  mem_signFixed_iff.2 fun g hg ↦ by rw [← (mem_invariants_signedPermRep_iff hε).1 hf, hg]

/-- The vector `ε a x • m` attached to `a • x` does not depend on the choice of `a`, when `m` is
fixed by the stabilizer sign at `x`. -/
theorem smul_eq_smul_of_mem_signFixed {x : X} {m : M} (hm : m ∈ signFixed R ε x) {a b : G}
    (h : a • x = b • x) : ε a x • m = ε b x • m := by
  have hab : (b⁻¹ * a) • x = x := by rw [mul_smul, h, inv_smul_smul]
  have hε' := hε b (b⁻¹ * a) x
  rw [mul_inv_cancel_left, hab] at hε'
  rw [hε', mul_smul, mem_signFixed_iff.1 hm _ hab]

/-- The stabilizer sign at a point is trivial exactly when it is trivial at any other point of the
orbit: the stabilizer of `a • x` is the conjugate of the stabilizer of `x`, with conjugate signs. -/
theorem forall_smul_eq_imp_eq_one_smul_iff (a : G) (x : X) :
    (∀ g : G, g • a • x = a • x → ε g (a • x) = 1) ↔ ∀ g : G, g • x = x → ε g x = 1 := by
  -- on the stabilizer of `a • x`, the sign of `g` at `a • x` is the sign of `a⁻¹ * g * a` at `x`
  have key {g : G} (hg : g • a • x = a • x) : ε (a⁻¹ * g * a) x = ε g (a • x) := by
    have h1 : ε a⁻¹ (a • x) * ε a x = 1 := by
      rw [← hε, inv_mul_cancel, sign_one_of_cocycle hε]
    rw [hε, hε, hg, mul_right_comm, h1, one_mul]
  refine ⟨fun h g hg ↦ ?_, fun h g hg ↦ ?_⟩
  · have hg' : (a * g * a⁻¹) • a • x = a • x := by
      rw [mul_smul, mul_smul, inv_smul_smul, hg]
    have hconj : a⁻¹ * (a * g * a⁻¹) * a = g := by group
    rw [← hconj, key hg', h _ hg']
  · rw [← key hg]
    exact h _ (by rw [mul_smul, mul_smul, hg, inv_smul_smul])

/-! ### The orbit decomposition of the invariants -/

omit hε in
/-- The vector attached to `y` by the orbit vector of `m` at `x`: `ε a x • m` if `y = a • x`, and
`0` off the orbit of `x`. -/
private noncomputable def orbitValue (ε : G → X → ℤˣ) (x : X) (m : M) (y : X) : M :=
  open Classical in if h : y ∈ orbit G x then ε h.choose x • m else 0

private theorem orbitValue_eq {x : X} {m : M} (hm : m ∈ signFixed R ε x) {a : G} {y : X}
    (ha : a • x = y) : orbitValue ε x m y = ε a x • m := by
  have h : y ∈ orbit G x := ⟨a, ha⟩
  simp only [orbitValue, h, ↓reduceDIte]
  exact smul_eq_smul_of_mem_signFixed hε hm (h.choose_spec.trans ha.symm)

omit hε in
private theorem orbitValue_zero (x y : X) : orbitValue ε x (0 : M) y = 0 := by
  simp [orbitValue]

omit hε in
private theorem orbitValue_mk_out_ne_zero {c : orbitRel.Quotient G X →₀ M} {y : X}
    (hy : orbitValue ε (⟦y⟧ : orbitRel.Quotient G X).out (c ⟦y⟧) y ≠ 0) :
    ⟦y⟧ ∈ c.support := by
  rw [mem_support_iff]
  rintro h
  rw [h, orbitValue_zero] at hy
  exact hy rfl

omit hε in
private theorem finite_support_orbitValue (hfin : ∀ x : X, (orbit G x).Finite)
    (c : orbitRel.Quotient G X →₀ M) :
    (Function.support fun y ↦
      orbitValue ε (⟦y⟧ : orbitRel.Quotient G X).out (c ⟦y⟧) y).Finite := by
  refine (c.support.finite_toSet.biUnion fun ω _ ↦ hfin ω.out).subset
    fun y hy ↦ Set.mem_biUnion (orbitValue_mk_out_ne_zero hy) ?_
  obtain ⟨a, ha⟩ := MulAction.exists_smul_out_eq (ω := (⟦y⟧ : orbitRel.Quotient G X)) rfl
  exact ⟨a, ha⟩

variable (R M) in
/-- The finitely supported functions on the orbit space whose value at each orbit `ω` is fixed by
the stabilizer sign at the representative `ω.out`. -/
noncomputable def orbitSignFixed (ε : G → X → ℤˣ) :
    Submodule R (orbitRel.Quotient G X →₀ M) :=
  Finsupp.submodule fun ω ↦ signFixed R ε ω.out

omit hε in
@[simp]
theorem mem_orbitSignFixed_iff {c : orbitRel.Quotient G X →₀ M} :
    c ∈ orbitSignFixed R M ε ↔ ∀ ω, c ω ∈ signFixed R ε ω.out :=
  Finsupp.mem_submodule_iff _ _

/-- The invariant function with prescribed values at the orbit representatives. -/
private noncomputable def ofOrbitSignFixed (hfin : ∀ x : X, (orbit G x).Finite)
    (c : orbitSignFixed R M ε) : (signedPermRep R M ε hε).invariants :=
  ⟨ofSupportFinite _ (finite_support_orbitValue hfin (c : orbitRel.Quotient G X →₀ M)), by
    refine (mem_invariants_signedPermRep_iff hε).2 fun g x ↦ ?_
    obtain ⟨a, ha⟩ := MulAction.exists_smul_out_eq (ω := (⟦x⟧ : orbitRel.Quotient G X)) rfl
    have hc := mem_orbitSignFixed_iff.1 c.property ⟦x⟧
    have hga : (g * a) • (⟦x⟧ : orbitRel.Quotient G X).out = g • x := by rw [mul_smul, ha]
    simp only [ofSupportFinite_coe, orbitRel.Quotient.quotient_smul_eq]
    rw [orbitValue_eq hε hc ha, orbitValue_eq hε hc hga, hε, ha, mul_smul]⟩

private theorem ofOrbitSignFixed_apply_smul_out (hfin : ∀ x : X, (orbit G x).Finite)
    (c : orbitSignFixed R M ε) (ω : orbitRel.Quotient G X) (a : G) :
    ((ofOrbitSignFixed hε hfin c : _) : X →₀ M) (a • ω.out) =
      ε a ω.out • (c : orbitRel.Quotient G X →₀ M) ω := by
  simp only [ofOrbitSignFixed, ofSupportFinite_coe, orbitRel.Quotient.quotient_smul_eq,
    Quotient.out_eq]
  exact orbitValue_eq hε (mem_orbitSignFixed_iff.1 c.property ω) rfl

variable (R M) in
/-- **The orbit decomposition of the invariants.** When every orbit is finite, an invariant
function of the signed permutation representation is determined by its values at the orbit
representatives, and these values can be any vectors fixed by the stabilizer signs there. For a
finite group, take `hfin := Finite.finite_mulAction_orbit`. -/
noncomputable def invariantsSignedPermRepEquiv (hfin : ∀ x : X, (orbit G x).Finite) :
    (signedPermRep R M ε hε).invariants ≃ₗ[R] orbitSignFixed R M ε where
  toFun f := ⟨(f : X →₀ M).comapDomain Quotient.out Quotient.out_injective.injOn,
    mem_orbitSignFixed_iff.2 fun ω ↦ by
      rw [comapDomain_apply]
      exact apply_mem_signFixed_of_mem_invariants hε f.property _⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun := ofOrbitSignFixed hε hfin
  left_inv f := Subtype.ext <| Finsupp.ext fun y ↦ by
    obtain ⟨a, ha⟩ := MulAction.exists_smul_out_eq (ω := (⟦y⟧ : orbitRel.Quotient G X)) rfl
    rw [← ha, ofOrbitSignFixed_apply_smul_out, (mem_invariants_signedPermRep_iff hε).1 f.property]
    exact congrArg _ (comapDomain_apply _ _ _ _)
  right_inv c := Subtype.ext <| Finsupp.ext fun ω ↦ by
    simpa [sign_one_of_cocycle hε] using ofOrbitSignFixed_apply_smul_out hε hfin c ω 1

/-- The value of the orbit coefficients of an invariant function at an orbit is its value at the
representative. -/
@[simp]
theorem invariantsSignedPermRepEquiv_apply (hfin : ∀ x : X, (orbit G x).Finite)
    (f : (signedPermRep R M ε hε).invariants) (ω : orbitRel.Quotient G X) :
    (invariantsSignedPermRepEquiv R M hε hfin f : orbitRel.Quotient G X →₀ M) ω =
      (f : X →₀ M) ω.out :=
  comapDomain_apply _ _ _ _

/-- The invariant function with orbit coefficients `c` has value `ε a ω.out • c ω` at
`a • ω.out`. -/
@[simp]
theorem invariantsSignedPermRepEquiv_symm_apply_smul_out (hfin : ∀ x : X, (orbit G x).Finite)
    (c : orbitSignFixed R M ε) (ω : orbitRel.Quotient G X) (a : G) :
    ((invariantsSignedPermRepEquiv R M hε hfin).symm c : X →₀ M) (a • ω.out) =
      ε a ω.out • (c : orbitRel.Quotient G X →₀ M) ω :=
  ofOrbitSignFixed_apply_smul_out hε hfin c ω a

/-! ### The orbits with trivial stabilizer sign -/

/-- The orbits on which the stabilizer sign is trivial, tested at the representative `ω.out`. Every
point of the orbit gives the same answer (`TauCeti.mk_mem_trivialSignOrbits_iff`). -/
def trivialSignOrbits (ε : G → X → ℤˣ) : Set (orbitRel.Quotient G X) :=
  {ω | ∀ g : G, g • ω.out = ω.out → ε g ω.out = 1}

omit hε in
theorem mem_trivialSignOrbits_iff {ω : orbitRel.Quotient G X} :
    ω ∈ trivialSignOrbits ε ↔ ∀ g : G, g • ω.out = ω.out → ε g ω.out = 1 :=
  Iff.rfl

/-- The orbit of `x` has trivial stabilizer sign exactly when the stabilizer sign at `x` is
trivial. -/
theorem mk_mem_trivialSignOrbits_iff (x : X) :
    ⟦x⟧ ∈ trivialSignOrbits ε ↔ ∀ g : G, g • x = x → ε g x = 1 := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_out_eq (ω := (⟦x⟧ : orbitRel.Quotient G X)) rfl
  have h := forall_smul_eq_imp_eq_one_smul_iff hε a (⟦x⟧ : orbitRel.Quotient G X).out
  rw [ha] at h
  exact mem_trivialSignOrbits_iff.trans h.symm

omit hε in
/-- When `2` is a nonzerodivisor on `M`, a function on the orbit space has values fixed by the
stabilizer signs exactly when it is supported on the orbits with trivial stabilizer sign. -/
theorem orbitSignFixed_eq_supported (h2 : IsSMulRegular M (2 : R)) :
    orbitSignFixed R M ε = supported M R (trivialSignOrbits ε) := by
  ext c
  rw [mem_orbitSignFixed_iff, mem_supported']
  refine ⟨fun hc ω hω ↦ ?_, fun hc ω ↦ ?_⟩
  · have h : ∃ g : G, g • ω.out = ω.out ∧ ε g ω.out ≠ 1 := by
      simpa [mem_trivialSignOrbits_iff, not_forall] using hω
    simpa [signFixed_eq_bot h2 h] using hc ω
  · by_cases hω : ω ∈ trivialSignOrbits ε
    · rw [signFixed_eq_top (mem_trivialSignOrbits_iff.1 hω)]
      exact Submodule.mem_top
    · rw [hc ω hω]
      exact zero_mem _

variable (R M) in
/-- **The orbit basis of invariant chains with sign coefficients.** When every orbit is finite and
`2` is a nonzerodivisor on `M`, the invariants of the signed permutation representation are the
finitely supported functions with values in `M` on the orbits whose stabilizer sign is trivial; the
other orbits contribute nothing. -/
noncomputable def invariantsSignedPermRepEquivFinsupp (hfin : ∀ x : X, (orbit G x).Finite)
    (h2 : IsSMulRegular M (2 : R)) :
    (signedPermRep R M ε hε).invariants ≃ₗ[R] trivialSignOrbits ε →₀ M :=
  (invariantsSignedPermRepEquiv R M hε hfin).trans <|
    (LinearEquiv.ofEq _ _ (orbitSignFixed_eq_supported h2)).trans (supportedEquivFinsupp _)

/-- The coefficient of the image of an invariant function at an orbit with trivial stabilizer sign
is its value at the representative. -/
@[simp]
theorem invariantsSignedPermRepEquivFinsupp_apply (hfin : ∀ x : X, (orbit G x).Finite)
    (h2 : IsSMulRegular M (2 : R)) (f : (signedPermRep R M ε hε).invariants)
    (ω : trivialSignOrbits ε) :
    invariantsSignedPermRepEquivFinsupp R M hε hfin h2 f ω = (f : X →₀ M) ω.val.out := by
  simp [invariantsSignedPermRepEquivFinsupp]

/-- The invariant function with coefficients `c` on the orbits with trivial stabilizer sign has
value `ε a ω.out • c ω` at `a • ω.out`. -/
@[simp]
theorem invariantsSignedPermRepEquivFinsupp_symm_apply_smul_out
    (hfin : ∀ x : X, (orbit G x).Finite) (h2 : IsSMulRegular M (2 : R))
    (c : trivialSignOrbits ε →₀ M) (ω : trivialSignOrbits ε) (a : G) :
    ((invariantsSignedPermRepEquivFinsupp R M hε hfin h2).symm c : X →₀ M) (a • ω.val.out) =
      ε a ω.val.out • c ω := by
  classical
  simp [invariantsSignedPermRepEquivFinsupp]

/-- The invariant function with coefficients `c` on the orbits with trivial stabilizer sign
vanishes at the points of the other orbits. -/
theorem invariantsSignedPermRepEquivFinsupp_symm_apply_eq_zero
    (hfin : ∀ x : X, (orbit G x).Finite) (h2 : IsSMulRegular M (2 : R))
    (c : trivialSignOrbits ε →₀ M) {x : X} (hx : ⟦x⟧ ∉ trivialSignOrbits ε) :
    ((invariantsSignedPermRepEquivFinsupp R M hε hfin h2).symm c : X →₀ M) x = 0 := by
  have hf := apply_mem_signFixed_of_mem_invariants hε
    ((invariantsSignedPermRepEquivFinsupp R M hε hfin h2).symm c).property x
  rw [mk_mem_trivialSignOrbits_iff hε] at hx
  push Not at hx
  simpa [signFixed_eq_bot h2 hx] using hf

end Group

end TauCeti
