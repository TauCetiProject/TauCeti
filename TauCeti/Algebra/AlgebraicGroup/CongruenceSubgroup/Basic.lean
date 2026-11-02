/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Filtration
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Principal congruence subgroups of the points of a Hopf algebra

Let `H` be a Hopf algebra over `k`, not necessarily commutative. The convolution groups
`G(R) = WithConv (H →ₐ[k] R)`, for commutative `k`-algebras `R`, form a group-valued functor `G`
of `R`; when `H` is commutative, `G(R)` is the group of `R`-points of the affine group scheme
`Spec H`. For an ideal `I` of `R`, the **principal congruence subgroup** of level `I` is the kernel

  `G(R)_I = ker (G(R) → G(R ⧸ I))`

of reduction modulo `I`. When `H` is commutative and `R = k = O` is the valuation ring of a
nonarchimedean local field with maximal ideal `m` and `I = m ^ n`, these are the congruence
subgroups `𝒢(O)ₙ` of the integral model `𝒢 = Spec H`, the level subgroups of the smooth
representation theory of `p`-adic groups.

## Main declarations

* `TauCeti.HopfAlgebra.congruenceSubgroup k H I`: the kernel of reduction modulo `I`, a normal
  subgroup of `WithConv (H →ₐ[k] R)`.
* `TauCeti.HopfAlgebra.mem_congruenceSubgroup_iff`: `x` lies in `G(R)_I` exactly when `x` and the
  identity point agree modulo `I`; `mem_congruenceSubgroup_iff_of_adjoin_eq_top` checks this on a
  generating set of `H`.
* `TauCeti.HopfAlgebra.congruenceSubgroup_mono`, `congruenceSubgroup_top`,
  `congruenceSubgroup_bot`, `congruenceSubgroup_inf` and `congruenceSubgroup_iInf`: the level map
  `I ↦ G(R)_I` is monotone and preserves the top element, the bottom element and infima.
* `TauCeti.HopfAlgebra.iInf_congruenceSubgroup_pow_eq_bot`: over a noetherian local ring, the
  congruence subgroups of the levels `I ^ n` for a proper ideal `I` intersect trivially.
* `TauCeti.HopfAlgebra.congruenceSubgroup_le_comap_mapDomain` and
  `congruenceSubgroup_le_comap_mapValue`: homomorphisms of groups and compatible maps of coefficient
  rings preserve congruence subgroups.

## References

* V. Platonov, A. Rapinchuk, I. Rapinchuk, *Algebraic groups and number theory*, vol. 1,
  2nd ed. (2023), §3.1, p. 126, and §3.3, (3.15), p. 160.
-/

public section

open Coalgebra WithConv

namespace TauCeti

namespace HopfAlgebra

variable {k H R : Type*} [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H]
  [CommRing R] [Algebra k R]

variable (k H) in
/-- The principal congruence subgroup of level `I` in the group of `R`-points of a Hopf algebra
`H`: the kernel of the reduction map `G(R) → G(R ⧸ I)` induced by the quotient map `R → R ⧸ I`. -/
noncomputable def congruenceSubgroup (I : Ideal R) : Subgroup (WithConv (H →ₐ[k] R)) :=
  (AlgHom.mapValue (H := H) (Ideal.Quotient.mkₐ k I)).ker

/-- A point lies in the congruence subgroup of level `I` exactly when it reduces to the identity
modulo `I`. -/
theorem mem_congruenceSubgroup_iff_mapValue_eq_one {I : Ideal R} {x : WithConv (H →ₐ[k] R)} :
    x ∈ congruenceSubgroup k H I ↔ AlgHom.mapValue (Ideal.Quotient.mkₐ k I) x = 1 :=
  MonoidHom.mem_ker

/-- A point `x` lies in the congruence subgroup of level `I` exactly when it agrees with the
identity point `algebraMap k R ∘ ε` modulo `I`. -/
theorem mem_congruenceSubgroup_iff {I : Ideal R} {x : WithConv (H →ₐ[k] R)} :
    x ∈ congruenceSubgroup k H I ↔ ∀ h, x.ofConv h - algebraMap k R (counit h) ∈ I := by
  rw [mem_congruenceSubgroup_iff_mapValue_eq_one, AlgHom.mapValue_apply, WithConv.ext_iff,
    ofConv_toConv, AlgHom.ext_iff]
  refine forall_congr' fun h ↦ ?_
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.convOne_apply,
    ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]

/-- Membership in a congruence subgroup can be tested on a set of algebra generators of `H`. -/
theorem mem_congruenceSubgroup_iff_of_adjoin_eq_top {s : Set H} (hs : Algebra.adjoin k s = ⊤)
    {I : Ideal R} {x : WithConv (H →ₐ[k] R)} :
    x ∈ congruenceSubgroup k H I ↔ ∀ h ∈ s, x.ofConv h - algebraMap k R (counit h) ∈ I := by
  refine ⟨fun hx h _ ↦ mem_congruenceSubgroup_iff.1 hx h, fun hx ↦ ?_⟩
  rw [mem_congruenceSubgroup_iff_mapValue_eq_one, AlgHom.mapValue_apply, WithConv.ext_iff,
    ofConv_toConv]
  refine AlgHom.ext_of_adjoin_eq_top hs fun h hh ↦ ?_
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.convOne_apply,
    ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  exact hx h hh

/-- Congruence subgroups are normal: they are kernels of group homomorphisms. -/
instance congruenceSubgroup_normal (I : Ideal R) : (congruenceSubgroup k H I).Normal :=
  MonoidHom.normal_ker _

variable (k H R)

/-- The congruence subgroup grows with its level: `I ≤ J` implies `G(R)_I ≤ G(R)_J`. In
particular the subgroups of the levels `I ^ n` decrease with `n`. -/
theorem congruenceSubgroup_mono : Monotone (congruenceSubgroup k H (R := R)) :=
  fun _ _ hIJ _ hx ↦ mem_congruenceSubgroup_iff.2 fun h ↦ hIJ (mem_congruenceSubgroup_iff.1 hx h)

/-- The congruence subgroup of level `⊤` is the whole group of points. -/
@[simp]
theorem congruenceSubgroup_top : congruenceSubgroup k H (⊤ : Ideal R) = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_congruenceSubgroup_iff.2 fun _ ↦ Submodule.mem_top

/-- The congruence subgroup of level `⊥` is trivial: reduction modulo the zero ideal is
injective. -/
@[simp]
theorem congruenceSubgroup_bot : congruenceSubgroup k H (⊥ : Ideal R) = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ Subgroup.mem_bot.2 ?_
  refine ofConv_injective (AlgHom.ext fun h ↦ ?_)
  rw [← sub_eq_zero, ← Ideal.mem_bot]
  simpa only [AlgHom.convOne_apply] using mem_congruenceSubgroup_iff.1 hx h

variable {k H R}

/-- The congruence subgroup of an intersection of two levels is the intersection of the
congruence subgroups. -/
@[simp]
theorem congruenceSubgroup_inf (I J : Ideal R) :
    congruenceSubgroup k H (I ⊓ J) = congruenceSubgroup k H I ⊓ congruenceSubgroup k H J := by
  ext x
  simp only [Subgroup.mem_inf, mem_congruenceSubgroup_iff, Submodule.mem_inf, forall_and]

/-- The congruence subgroup of an intersection of levels is the intersection of the congruence
subgroups. -/
@[simp]
theorem congruenceSubgroup_iInf {ι : Sort*} (I : ι → Ideal R) :
    congruenceSubgroup k H (⨅ i, I i) = ⨅ i, congruenceSubgroup k H (I i) := by
  ext x
  simp only [Subgroup.mem_iInf, mem_congruenceSubgroup_iff, Submodule.mem_iInf]
  exact forall_comm

variable (k H) in
/-- **Krull intersection for congruence subgroups.** Over a noetherian local ring `R`, the
congruence subgroups of the levels `I ^ n` of a proper ideal `I` intersect in the identity. For
the valuation ring `O` of a nonarchimedean local field and its maximal ideal, this is
`⋂ₙ 𝒢(O)ₙ = 1`. -/
theorem iInf_congruenceSubgroup_pow_eq_bot [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R}
    (hI : I ≠ ⊤) : ⨅ n : ℕ, congruenceSubgroup k H (I ^ n) = ⊥ := by
  rw [← congruenceSubgroup_iInf, Ideal.iInf_pow_eq_bot_of_isLocalRing I hI,
    congruenceSubgroup_bot]

/-- A homomorphism of affine groups preserves congruence subgroups: pre-composition with a
bialgebra map `φ : H₁ →ₐc[k] H₂` carries the congruence subgroup of `H₂` of level `I` into that
of `H₁`. -/
theorem congruenceSubgroup_le_comap_mapDomain {H₁ H₂ : Type*} [Semiring H₁]
    [_root_.HopfAlgebra k H₁] [Semiring H₂] [_root_.HopfAlgebra k H₂] (φ : H₁ →ₐc[k] H₂)
    (I : Ideal R) :
    congruenceSubgroup k H₂ I ≤ (congruenceSubgroup k H₁ I).comap (BialgHom.mapDomain φ) := by
  intro x hx
  rw [Subgroup.mem_comap, mem_congruenceSubgroup_iff_mapValue_eq_one,
    ← MonoidHom.comp_apply, ← BialgHom.mapValue_mapDomain, MonoidHom.comp_apply,
    mem_congruenceSubgroup_iff_mapValue_eq_one.1 hx, map_one]

/-- A map of coefficient rings `ψ : R →ₐ[k] R'` carrying `I` into `J` carries the congruence
subgroup of level `I` into the congruence subgroup of level `J`. -/
theorem congruenceSubgroup_le_comap_mapValue {R' : Type*} [CommRing R'] [Algebra k R']
    (ψ : R →ₐ[k] R') {I : Ideal R} {J : Ideal R'} (hIJ : I ≤ J.comap ψ) :
    congruenceSubgroup k H I ≤ (congruenceSubgroup k H J).comap (AlgHom.mapValue ψ) := by
  intro x hx
  rw [Subgroup.mem_comap, mem_congruenceSubgroup_iff]
  intro h
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, ← AlgHom.commutes ψ, ← map_sub]
  exact hIJ (mem_congruenceSubgroup_iff.1 hx h)

end HopfAlgebra

end TauCeti
