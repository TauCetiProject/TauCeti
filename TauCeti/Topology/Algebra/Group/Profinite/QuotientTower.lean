/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti AI contributors
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Algebra.Group.Profinite.Limit

/-!
# Towers of finite quotients of a topological group

A *tower of finite quotients* of a topological group `Γ` is a sequence of continuous surjective
homomorphisms `q n : Γ → A n` onto discrete groups, with transition homomorphisms
`t h : A n → A m` for `m ≤ n` satisfying `t h ∘ q n = q m`, whose kernels separate the points of
`Γ`. Over a compact group such a tower is a countable presentation of `Γ` by finite quotients:
the groups `A n` are finite, the kernels `ker q n` form a decreasing neighbourhood basis of `1`,
so every open subgroup contains one of them, and every locally constant function on `Γ` factors
through some `q n`. The units `ℤ_pˣ` with their reductions modulo `p ^ n`, and `ℤ_p` with its
truncations, are the basic examples.

Such a tower is how measures on `Γ` and elements of the completed group algebra of `Γ` are
described by countably many finite coordinates: test functions that are locally constant descend
to some finite level `A n`, and the finite levels are cofinal among all the finite quotients
`Γ ⧸ U` by open normal subgroups.

## Main definitions

* `TauCeti.FiniteQuotientTower Γ A`: a tower of discrete quotients `q n : Γ →ₜ* A n` with
  transition homomorphisms and point-separating kernels.
* `TauCeti.FiniteQuotientTower.ker`: the kernel of `q n`, as an open normal subgroup.
* `TauCeti.FiniteQuotientTower.toQuotient`: for a normal subgroup `U` containing the kernel of
  `q n`, the homomorphism `A n →* Γ ⧸ U` through which the quotient map factors.
* `TauCeti.FiniteQuotientTower.compatibleFamilies`: the families of finitely supported
  coefficients on the levels that are compatible under the transition maps; these are the
  coordinates of measures on `Γ`.

## Main results

* `TauCeti.FiniteQuotientTower.ext`: a tower is determined by its projections; the transition
  homomorphisms are forced by surjectivity.
* `TauCeti.FiniteQuotientTower.t_t`: the transition homomorphisms compose.
* `TauCeti.FiniteQuotientTower.totallyDisconnectedSpace`: a group with a tower is totally
  disconnected.
* `TauCeti.FiniteQuotientTower.hasAntitoneBasis_nhds_one`: over a compact group the kernels form
  a decreasing neighbourhood basis of `1`.
* `TauCeti.FiniteQuotientTower.exists_ker_le_of_isOpen`: every open subgroup of a compact group
  contains the kernel of some level.
* `TauCeti.FiniteQuotientTower.exists_comp_q_eq`: every locally constant function on a compact
  group factors through some level.
* `TauCeti.FiniteQuotientTower.exists_monoidHom_comp_q_eq`: every locally constant homomorphism
  factors through some level by a homomorphism.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Ann. Math. Qué.
  (2024), Proposition 3.16, where measures on a profinite group are described through a tower of
  finite quotients.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.1.
-/

public section

open Filter Topology

namespace TauCeti

/-- A **tower of finite quotients** of a topological group `Γ`: continuous surjective
homomorphisms `q n : Γ → A n` onto discrete groups, with transition homomorphisms
`t h : A n → A m` for `m ≤ n` compatible with the projections, such that the projections separate
the points of `Γ`.

The transition homomorphisms are determined by the projections (`FiniteQuotientTower.ext`).
When `Γ` is compact the groups `A n` are finite (`FiniteQuotientTower.finite`) and the kernels of
the projections are cofinal among the open subgroups
(`FiniteQuotientTower.exists_ker_le_of_isOpen`). -/
structure FiniteQuotientTower (Γ : Type*) [Group Γ] [TopologicalSpace Γ] (A : ℕ → Type*)
    [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)] [∀ n, DiscreteTopology (A n)] where
  /-- The projection onto the `n`-th quotient. -/
  q (n : ℕ) : Γ →ₜ* A n
  /-- Every projection is surjective. -/
  surjective_q (n : ℕ) : Function.Surjective (q n)
  /-- The transition homomorphism from level `n` down to a level `m ≤ n`. -/
  t {m n : ℕ} (h : m ≤ n) : A n →* A m
  /-- The transition homomorphisms are compatible with the projections. -/
  t_q {m n : ℕ} (h : m ≤ n) (x : Γ) : t h (q n x) = q m x
  /-- The projections separate points: a nontrivial element has a nontrivial image at some
  level. -/
  separates {x : Γ} (hx : x ≠ 1) : ∃ n, q n x ≠ 1

namespace FiniteQuotientTower

attribute [simp] t_q

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {A : ℕ → Type*} [∀ n, Group (A n)]
  [∀ n, TopologicalSpace (A n)] [∀ n, DiscreteTopology (A n)]

/-- A tower is determined by its projections: the transition homomorphisms are forced by the
surjectivity of the projections. -/
@[ext]
theorem ext {T T' : FiniteQuotientTower Γ A} (h : ∀ n, T.q n = T'.q n) : T = T' := by
  have ht {m n : ℕ} (hmn : m ≤ n) : T.t hmn = T'.t hmn := MonoidHom.ext fun a ↦ by
    obtain ⟨x, rfl⟩ := T.surjective_q n a
    rw [T.t_q, h, h, T'.t_q]
  revert h ht
  obtain ⟨q, -, t, -, -⟩ := T
  obtain ⟨q', -, t', -, -⟩ := T'
  intro h ht
  obtain rfl : q = q' := funext h
  obtain rfl : @t = @t' := by
    funext m n hmn
    exact ht hmn
  rfl

variable (T : FiniteQuotientTower Γ A)

/-- The compatibility of a transition homomorphism with the projections, as an equation of
homomorphisms. -/
theorem t_comp_q {m n : ℕ} (h : m ≤ n) :
    (T.t h).comp (T.q n : Γ →* A n) = (T.q m : Γ →* A m) :=
  MonoidHom.ext (T.t_q h)

/-- The transition homomorphism from a level to itself is the identity. -/
@[simp]
theorem t_self {n : ℕ} (h : n ≤ n) (a : A n) : T.t h a = a := by
  obtain ⟨x, rfl⟩ := T.surjective_q n a
  exact T.t_q h x

/-- The transition homomorphisms compose: going down from `n` to `m` and then to `k` is going
down from `n` to `k`. -/
@[simp]
theorem t_t {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (a : A n) :
    T.t hkm (T.t hmn a) = T.t (hkm.trans hmn) a := by
  obtain ⟨x, rfl⟩ := T.surjective_q n a
  simp

/-- The transition homomorphisms compose, as an equation of homomorphisms. -/
theorem t_comp_t {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (T.t hkm).comp (T.t hmn) = T.t (hkm.trans hmn) :=
  MonoidHom.ext (T.t_t hkm hmn)

/-- Every transition homomorphism is surjective. -/
theorem t_surjective {m n : ℕ} (h : m ≤ n) : Function.Surjective (T.t h) := fun a ↦ by
  obtain ⟨x, rfl⟩ := T.surjective_q m a
  exact ⟨T.q n x, T.t_q h x⟩

/-- Two elements with the same image at every level are equal. -/
theorem eq_of_forall_q_eq {x y : Γ} (h : ∀ n, T.q n x = T.q n y) : x = y := by
  by_contra hxy
  obtain ⟨n, hn⟩ := T.separates (x := x⁻¹ * y) fun h' ↦ hxy (inv_mul_eq_one.mp h')
  exact hn (by rw [map_mul, map_inv, h n, inv_mul_cancel])

include T in
/-- A group with a tower of finite quotients is totally disconnected: the projections are
constant on every preconnected set, and they separate points. -/
theorem totallyDisconnectedSpace : TotallyDisconnectedSpace Γ where
  isTotallyDisconnected_univ _ _ hs _ hx _ hy :=
    T.eq_of_forall_q_eq fun n ↦ hs.constant (T.q n).continuous.continuousOn hx hy

include T in
/-- Over a compact group the quotients of a tower are finite. -/
theorem finite [CompactSpace Γ] (n : ℕ) : Finite (A n) :=
  have : CompactSpace (A n) := (T.surjective_q n).compactSpace (T.q n).continuous
  finite_of_compact_of_discrete

/-! ### The kernels of a tower -/

/-- The kernel of the projection onto the `n`-th quotient, an open normal subgroup since the
quotient is discrete. -/
def ker (n : ℕ) : OpenNormalSubgroup Γ where
  toSubgroup := (T.q n : Γ →* A n).ker
  isOpen' := (isOpen_discrete {1}).preimage (T.q n).continuous
  isNormal' := MonoidHom.normal_ker _

/-- An element lies in the `n`-th kernel exactly when its image at level `n` is trivial. -/
@[simp]
theorem mem_ker {n : ℕ} {x : Γ} : x ∈ T.ker n ↔ T.q n x = 1 :=
  MonoidHom.mem_ker

/-- Membership in the kernel of a level, read through the underlying open subgroup; this is the
form that membership in `(T.ker n : Subgroup Γ)` takes after simplification. -/
@[simp]
theorem mem_toOpenSubgroup_ker {n : ℕ} {x : Γ} : x ∈ (T.ker n).toOpenSubgroup ↔ T.q n x = 1 :=
  MonoidHom.mem_ker

/-- The subgroup underlying the `n`-th kernel is the kernel of the `n`-th projection. -/
theorem toSubgroup_ker (n : ℕ) : (T.ker n : Subgroup Γ) = (T.q n : Γ →* A n).ker :=
  (rfl)

/-- The kernels of a tower decrease. -/
theorem ker_antitone : Antitone T.ker := fun m n h x hx ↦ by
  rw [mem_ker] at hx ⊢
  rw [← T.t_q h, hx, map_one]

/-- The kernels of a tower have trivial intersection. -/
theorem iInf_ker_eq_bot : ⨅ n, (T.ker n : Subgroup Γ) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx ↦ T.eq_of_forall_q_eq fun n ↦ ?_
  rw [map_one]
  exact T.mem_ker.mp (Subgroup.mem_iInf.mp hx n)

/-- **The kernels of a tower of a compact group are a neighbourhood basis of `1`.** -/
theorem hasAntitoneBasis_nhds_one [SeparatelyContinuousMul Γ] [CompactSpace Γ] :
    (𝓝 (1 : Γ)).HasAntitoneBasis fun n ↦ (T.ker n : Set Γ) :=
  hasAntitoneBasis_nhds_one_of_iInf_eq_bot (N := fun n ↦ (T.ker n : Subgroup Γ))
    (fun _ _ h ↦ T.ker_antitone h) (fun n ↦ (T.ker n).isOpen) T.iInf_ker_eq_bot

/-- **Cofinality of the kernels.** Every open subgroup of a compact group contains the kernel of
some level of a tower. -/
theorem exists_ker_le_of_isOpen [SeparatelyContinuousMul Γ] [CompactSpace Γ] {U : Subgroup Γ}
    (hU : IsOpen (U : Set Γ)) : ∃ n, (T.ker n : Subgroup Γ) ≤ U :=
  (T.hasAntitoneBasis_nhds_one.mem_iff.mp (hU.mem_nhds U.one_mem)).imp fun _ hn ↦
    SetLike.coe_subset_coe.mp hn

/-! ### Quotients coarser than a level -/

/-- For a normal subgroup `U` containing the `n`-th kernel, the homomorphism `A n →* Γ ⧸ U`
through which the quotient map `Γ → Γ ⧸ U` factors (`toQuotient_q`). -/
noncomputable def toQuotient {n : ℕ} {U : Subgroup Γ} [U.Normal] (h : (T.ker n : Subgroup Γ) ≤ U) :
    A n →* Γ ⧸ U :=
  (T.q n : Γ →* A n).liftOfSurjective (T.surjective_q n)
    ⟨QuotientGroup.mk' U, by rwa [QuotientGroup.ker_mk']⟩

/-- The homomorphism `A n →* Γ ⧸ U` sends the image of `x` at level `n` to the coset of `x`. -/
@[simp]
theorem toQuotient_q {n : ℕ} {U : Subgroup Γ} [U.Normal] (h : (T.ker n : Subgroup Γ) ≤ U)
    (x : Γ) : T.toQuotient h (T.q n x) = x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- Factoring the quotient map through a deeper level is compatible with the transition
homomorphism. -/
@[simp]
theorem toQuotient_t {m n : ℕ} (hmn : m ≤ n) {U : Subgroup Γ} [U.Normal]
    (h : (T.ker m : Subgroup Γ) ≤ U) (a : A n) :
    T.toQuotient h (T.t hmn a) =
      T.toQuotient (le_trans (α := Subgroup Γ) (T.ker_antitone hmn) h) a := by
  obtain ⟨x, rfl⟩ := T.surjective_q n a
  simp

/-- At the `n`-th kernel itself, the homomorphism `A n →* Γ ⧸ ker q n` is injective. -/
theorem toQuotient_injective (n : ℕ) :
    Function.Injective (T.toQuotient (le_refl (T.ker n : Subgroup Γ))) := fun a b hab ↦ by
  obtain ⟨x, rfl⟩ := T.surjective_q n a
  obtain ⟨y, rfl⟩ := T.surjective_q n b
  rw [toQuotient_q, toQuotient_q, QuotientGroup.eq] at hab
  have hq := T.mem_ker.mp hab
  rwa [map_mul, map_inv, inv_mul_eq_one] at hq

/-! ### Functions factoring through a level -/

variable {B : Type*}

/-- A function on `Γ` factors through the `n`-th projection of a tower exactly when it is
invariant under right translation by the `n`-th kernel. -/
theorem exists_comp_q_eq_iff {n : ℕ} {f : Γ → B} :
    (∃ g : A n → B, g ∘ T.q n = f) ↔ ∀ x, ∀ k ∈ T.ker n, f (x * k) = f x := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨g, rfl⟩ x k hk
    simp [T.mem_ker.mp hk]
  · have : Nonempty B := ⟨f 1⟩
    obtain ⟨g, hg⟩ := (Function.factorsThrough_iff (f := ⇑(T.q n)) f).mp fun x y hxy ↦ by
      rw [← hf x (x⁻¹ * y) (T.mem_ker.mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel])),
        mul_inv_cancel_left]
    exact ⟨g, hg.symm⟩

/-- A function that factors through the `m`-th projection of a tower factors through every
deeper projection. -/
theorem exists_comp_q_eq_of_le {m n : ℕ} (h : m ≤ n) {f : Γ → B}
    (hf : ∃ g : A m → B, g ∘ T.q m = f) : ∃ g : A n → B, g ∘ T.q n = f := by
  obtain ⟨g, rfl⟩ := hf
  exact ⟨g ∘ T.t h, by ext x; simp⟩

/-- **Descent of locally constant functions.** Every locally constant function on a compact
group, with values in any type, factors through some level of a tower. This applies in particular
to every continuous map to a discrete space, by `IsLocallyConstant.iff_continuous`. -/
theorem exists_comp_q_eq [ContinuousMul Γ] [CompactSpace Γ] {f : Γ → B}
    (hf : IsLocallyConstant f) : ∃ n, ∃ g : A n → B, g ∘ T.q n = f := by
  -- The right-translation stabilizer of `f` is open, so it contains the kernel of some level.
  obtain ⟨n, hn⟩ := T.exists_ker_le_of_isOpen (isOpen_rightTranslationStabilizer hf)
  exact ⟨n, T.exists_comp_q_eq_iff.mpr fun x k hk ↦ mem_rightTranslationStabilizer.mp (hn hk) x⟩

/-- Every locally constant homomorphism from a compact group to a monoid factors through some
level of a tower by a homomorphism. This applies in particular to the quotient map onto `Γ ⧸ U`
for an open normal subgroup `U`, so the levels of a tower are cofinal among the finite quotients
of `Γ`. -/
theorem exists_monoidHom_comp_q_eq [ContinuousMul Γ] [CompactSpace Γ] [Monoid B] {f : Γ →* B}
    (hf : IsLocallyConstant f) :
    ∃ n, ∃ g : A n →* B, g.comp (T.q n : Γ →* A n) = f := by
  obtain ⟨n, g, hg⟩ := T.exists_comp_q_eq hf
  have hgq (x : Γ) : g (T.q n x) = f x := congrFun hg x
  refine ⟨n, { toFun := g, map_one' := ?_, map_mul' := fun a b ↦ ?_ }, ?_⟩
  · rw [← map_one (T.q n), hgq, map_one]
  · obtain ⟨x, rfl⟩ := T.surjective_q n a
    obtain ⟨y, rfl⟩ := T.surjective_q n b
    rw [← map_mul, hgq, hgq, hgq, map_mul]
  · ext x
    simp [hgq]

/-! ### Compatible families of coefficients -/

/-- The **compatible families** along a tower: the families of finitely supported coefficients
`c n : A n →₀ R` such that pushing `c n` forward along the transition map to a level `m ≤ n`,
which sums the coefficients over each fibre, gives `c m`. -/
def compatibleFamilies (R : Type*) [Semiring R] : Submodule R (∀ n, A n →₀ R) where
  carrier := {c | ∀ ⦃m n : ℕ⦄ (h : m ≤ n), (c n).mapDomain (T.t h) = c m}
  add_mem' {c d} hc hd m n h := by
    rw [Pi.add_apply, Pi.add_apply, Finsupp.mapDomain_add, hc h, hd h]
  zero_mem' m n h := by
    rw [Pi.zero_apply, Pi.zero_apply, Finsupp.mapDomain_zero]
  smul_mem' r c hc m n h := by
    rw [Pi.smul_apply, Pi.smul_apply, Finsupp.mapDomain_smul, hc h]

variable {T} in
/-- A family is compatible when its pushforward from every level to every lower level is the
family at the lower level. -/
@[simp]
theorem mem_compatibleFamilies {R : Type*} [Semiring R] {c : ∀ n, A n →₀ R} :
    c ∈ T.compatibleFamilies R ↔ ∀ ⦃m n : ℕ⦄ (h : m ≤ n), (c n).mapDomain (T.t h) = c m :=
  Iff.rfl

end FiniteQuotientTower

end TauCeti
