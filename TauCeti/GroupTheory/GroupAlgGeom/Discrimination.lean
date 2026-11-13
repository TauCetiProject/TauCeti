/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.GroupAlgGeom.Basic
import TauCeti.GroupTheory.FreeGroup.CSA

/-!
# Separation and discrimination of groups with coefficients

A group under `G` is separated by another when each nonidentity element survives under some
homomorphism fixing `G`. Discrimination asks for one homomorphism to preserve every element of
any given finite family simultaneously. The latter is the relative version of full residuality
used to recognize irreducible coordinate groups and, with trivial coefficients, limit groups.

The coefficient maps need not be injective: the same definitions apply to the coefficient maps
of quotients of free `G`-groups, even before the quotient is known to be a `G`-group.

Discrimination implies separation, but not conversely. A group discriminated by a commutative
transitive group, such as a free group, is commutative transitive, while the product of a
nonabelian group and a nontrivial group is not. So `F₂ × F₂` is separated by `F₂` through its two
projections, but not discriminated by it: for basis elements `a` and `b` of `F₂`, a homomorphism
to `F₂` keeping `(1, b)` nontrivial makes the images of `(a, 1)` and `(b, 1)` commute, so it kills
`(⁅a, b⁆, 1)`.

## Main results

* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.isSeparatedBy`: discrimination implies separation.
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.trans`, `TauCeti.GroupAlgGeom.IsSeparatedBy.trans`:
  discrimination and separation are transitive.
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.comp`, `TauCeti.GroupAlgGeom.IsSeparatedBy.comp`:
  discrimination and separation survive restriction of the coefficients.
* `TauCeti.GroupAlgGeom.IsSeparatedBy.prod`: a product of groups separated by `H` is separated by
  `H`, through the two projections.
* `TauCeti.GroupAlgGeom.IsSeparatedBy.isMulTorsionFree`: a group separated by a torsion-free
  group is torsion-free, so a nontrivial finite group is not separated by a torsion-free group
  (`TauCeti.GroupAlgGeom.not_isSeparatedBy_of_finite`); for instance `ℤ/2` is not separated by `ℤ`
  (`TauCeti.GroupAlgGeom.not_isSeparatedBy_zmod_two_int`).
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.isCommTransitive`: a group discriminated by a
  commutative transitive group is commutative transitive, so the product of a nonabelian group
  and a nontrivial group is not discriminated by a commutative transitive group
  (`TauCeti.GroupAlgGeom.not_isDiscriminatedBy_prod_of_nontrivial`).
* `TauCeti.GroupAlgGeom.isSeparatedBy_freeGroup_prod_freeGroup`,
  `TauCeti.GroupAlgGeom.not_isDiscriminatedBy_freeGroup_prod_freeGroup`: `F₂ × F₂` is separated
  but not discriminated by `F₂`, with trivial coefficients.
* `TauCeti.GroupAlgGeom.IsSeparatedBy.nonempty_gHom`: a nontrivial group separated by `H` admits a
  coefficient-preserving homomorphism to `H`; with discrimination the group may be trivial
  (`TauCeti.GroupAlgGeom.IsDiscriminatedBy.nonempty_gHom`).
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.injective_of_injective`: a group discriminated by a
  `G`-group is a `G`-group.
* `TauCeti.GroupAlgGeom.isSeparatedBy_iff_iInf_ker`: separation by `H` means the kernels of all
  coefficient-preserving homomorphisms to `H` intersect trivially.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §1 and §2.3 (the remark after Theorem C1 that
  `F × F` is separated but not discriminated by a nonabelian free group `F`, due to
  B. Baumslag).
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5 and §2.6.
-/

public section

namespace TauCeti.GroupAlgGeom

variable {G K H L : Type*} [Group G] [Group K] [Group H] [Group L]

/-- `K` is separated by `H` over `G` when every nonidentity element of `K` survives in some
homomorphism to `H` fixing the coefficients. -/
def IsSeparatedBy (ιK : G →* K) (ιH : G →* H) : Prop :=
  ∀ k : K, k ≠ 1 → ∃ φ : GHom ιK ιH, φ k ≠ 1

/-- `K` is discriminated by `H` over `G` when any finite family of nonidentity elements of `K`
survives simultaneously under one homomorphism to `H` fixing the coefficients. -/
def IsDiscriminatedBy (ιK : G →* K) (ιH : G →* H) : Prop :=
  ∀ s : Finset K, (∀ k ∈ s, k ≠ 1) →
    ∃ φ : GHom ιK ιH, ∀ k ∈ s, φ k ≠ 1

/-- Characterization of separation by coefficient-preserving homomorphisms. -/
theorem isSeparatedBy_def (ιK : G →* K) (ιH : G →* H) :
    IsSeparatedBy ιK ιH ↔ ∀ k : K, k ≠ 1 → ∃ φ : GHom ιK ιH, φ k ≠ 1 :=
  Iff.rfl

/-- Characterization of discrimination by coefficient-preserving homomorphisms. -/
theorem isDiscriminatedBy_def (ιK : G →* K) (ιH : G →* H) :
    IsDiscriminatedBy ιK ιH ↔
      ∀ s : Finset K, (∀ k ∈ s, k ≠ 1) →
        ∃ φ : GHom ιK ιH, ∀ k ∈ s, φ k ≠ 1 :=
  Iff.rfl

namespace IsDiscriminatedBy

/-- Discrimination implies separation by testing a singleton. -/
theorem isSeparatedBy {ιK : G →* K} {ιH : G →* H}
    (h : IsDiscriminatedBy ιK ιH) : IsSeparatedBy ιK ιH := by
  classical
  intro k hk
  obtain ⟨φ, hφ⟩ := h {k} (by simpa using hk)
  exact ⟨φ, hφ k (by simp)⟩

/-- A group discriminated by `H` admits a coefficient-preserving homomorphism to `H`. -/
theorem nonempty_gHom {ιK : G →* K} {ιH : G →* H} (h : IsDiscriminatedBy ιK ιH) :
    Nonempty (GHom ιK ιH) :=
  let ⟨φ, _⟩ := h ∅ (by simp)
  ⟨φ⟩

/-- If `K` is discriminated by `H` over `G` and the coefficient map `ιH` is injective, so is
`ιK`. -/
theorem injective_of_injective {ιK : G →* K} {ιH : G →* H} (h : IsDiscriminatedBy ιK ιH)
    (hH : Function.Injective ιH) : Function.Injective ιK := by
  obtain ⟨φ⟩ := h.nonempty_gHom
  apply Function.Injective.of_comp (f := φ) (g := ιK)
  change Function.Injective ((φ : K →* H).comp ιK)
  rwa [φ.comp_coeff]

/-- The source of an injective coefficient-preserving map into a discriminated group is
discriminated by the same target. -/
theorem of_injective {ιK : G →* K} {ιL : G →* L} {ιH : G →* H}
    (h : IsDiscriminatedBy ιL ιH) (f : GHom ιK ιL) (hf : Function.Injective f) :
    IsDiscriminatedBy ιK ιH := by
  classical
  intro s hs
  obtain ⟨φ, hφ⟩ := h (s.image f) (by
    simpa only [Finset.forall_mem_image, map_ne_one_iff f hf] using hs)
  refine ⟨φ.comp f, ?_⟩
  intro k hk
  simpa [GHom.coe_comp] using hφ (f k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

/-- Every group with a coefficient map discriminates itself through the identity. -/
theorem self (ιK : G →* K) : IsDiscriminatedBy ιK ιK := by
  intro s hs
  exact ⟨GHom.id ιK, by simpa using hs⟩

/-- Discrimination is transitive: if `K` is discriminated by `L` and `L` by `H`, all over `G`,
then `K` is discriminated by `H`. -/
theorem trans {ιK : G →* K} {ιL : G →* L} {ιH : G →* H}
    (hKL : IsDiscriminatedBy ιK ιL) (hLH : IsDiscriminatedBy ιL ιH) :
    IsDiscriminatedBy ιK ιH := by
  classical
  intro s hs
  obtain ⟨φ, hφ⟩ := hKL s hs
  obtain ⟨ψ, hψ⟩ := hLH (s.image φ) (by simpa using hφ)
  exact ⟨ψ.comp φ, fun k hk => by
    simpa [GHom.coe_comp] using hψ (φ k) (Finset.mem_image_of_mem φ hk)⟩

/-- Discrimination survives restriction of the coefficients along any homomorphism
`f : G' →* G`. -/
theorem comp {G' : Type*} [Group G'] {ιK : G →* K} {ιH : G →* H}
    (h : IsDiscriminatedBy ιK ιH) (f : G' →* G) :
    IsDiscriminatedBy (ιK.comp f) (ιH.comp f) := by
  intro s hs
  obtain ⟨φ, hφ⟩ := h s hs
  exact ⟨⟨φ, fun g => φ.map_coeff (f g)⟩, hφ⟩

/-- A group discriminated by a commutative transitive group is commutative transitive: one
homomorphism keeps any two nonidentity elements nontrivial. -/
theorem isCommTransitive {ιK : G →* K} {ιH : G →* H} (h : IsDiscriminatedBy ιK ιH)
    (hH : Group.IsCommTransitive H) : Group.IsCommTransitive K := by
  classical
  refine hH.of_forall_exists_monoidHom fun a b ha hb => ?_
  obtain ⟨φ, hφ⟩ := h {a, b} (by simp [ha, hb])
  exact ⟨φ, hφ a (by simp), hφ b (by simp)⟩

end IsDiscriminatedBy

namespace IsSeparatedBy

/-- The source of an injective coefficient-preserving map into a separated group is separated
by the same target. -/
theorem of_injective {ιK : G →* K} {ιL : G →* L} {ιH : G →* H}
    (h : IsSeparatedBy ιL ιH) (f : GHom ιK ιL) (hf : Function.Injective f) :
    IsSeparatedBy ιK ιH := by
  intro k hk
  obtain ⟨φ, hφ⟩ := h (f k) ((map_ne_one_iff f hf).2 hk)
  exact ⟨φ.comp f, by simpa [GHom.coe_comp] using hφ⟩

/-- Separation is transitive: if `K` is separated by `L` and `L` by `H`, all over `G`, then `K`
is separated by `H`. -/
theorem trans {ιK : G →* K} {ιL : G →* L} {ιH : G →* H}
    (hKL : IsSeparatedBy ιK ιL) (hLH : IsSeparatedBy ιL ιH) : IsSeparatedBy ιK ιH := by
  intro k hk
  obtain ⟨φ, hφ⟩ := hKL k hk
  obtain ⟨ψ, hψ⟩ := hLH (φ k) hφ
  exact ⟨ψ.comp φ, by simpa [GHom.coe_comp] using hψ⟩

/-- Separation survives restriction of the coefficients along any homomorphism `f : G' →* G`. -/
theorem comp {G' : Type*} [Group G'] {ιK : G →* K} {ιH : G →* H}
    (h : IsSeparatedBy ιK ιH) (f : G' →* G) : IsSeparatedBy (ιK.comp f) (ιH.comp f) := by
  intro k hk
  obtain ⟨φ, hφ⟩ := h k hk
  exact ⟨⟨φ, fun g => φ.map_coeff (f g)⟩, hφ⟩

/-- A product of two groups separated by `H` is separated by `H`, through the two projections.
The coefficients of the product are the pair of the coefficients of the factors. -/
theorem prod {ιK : G →* K} {ιL : G →* L} {ιH : G →* H} (hK : IsSeparatedBy ιK ιH)
    (hL : IsSeparatedBy ιL ιH) : IsSeparatedBy (ιK.prod ιL) ιH := by
  rintro ⟨k, l⟩ hkl
  by_cases hk : k = 1
  · obtain ⟨φ, hφ⟩ := hL l fun hl => hkl (by simp [hk, hl])
    exact ⟨⟨(φ : L →* H).comp (MonoidHom.snd K L), fun _ => by simp⟩, by simpa using hφ⟩
  · obtain ⟨φ, hφ⟩ := hK k hk
    exact ⟨⟨(φ : K →* H).comp (MonoidHom.fst K L), fun _ => by simp⟩, by simpa using hφ⟩

/-- A group separated by a torsion-free group is torsion-free: a homomorphism keeping a
nonidentity element of finite order nontrivial would give one in `H`. -/
theorem isMulTorsionFree [IsMulTorsionFree H] {ιK : G →* K} {ιH : G →* H}
    (h : IsSeparatedBy ιK ιH) : IsMulTorsionFree K :=
  .of_not_isOfFinOrder fun k hk hfin =>
    let ⟨φ, hφ⟩ := h k hk
    not_isOfFinOrder_of_isMulTorsionFree hφ (MonoidHom.isOfFinOrder (φ : K →* H) hfin)

/-- A nontrivial group separated by `H` admits a coefficient-preserving homomorphism to `H`. -/
theorem nonempty_gHom [Nontrivial K] {ιK : G →* K} {ιH : G →* H}
    (h : IsSeparatedBy ιK ιH) : Nonempty (GHom ιK ιH) :=
  let ⟨k, hk⟩ := exists_ne (1 : K)
  ⟨((isSeparatedBy_def _ _).1 h k hk).choose⟩

end IsSeparatedBy

/-- A nontrivial finite group is not separated by a torsion-free group, whatever the
coefficients: its nonidentity elements have finite order. -/
theorem not_isSeparatedBy_of_finite [Finite K] [Nontrivial K] [IsMulTorsionFree H] (ιK : G →* K)
    (ιH : G →* H) : ¬IsSeparatedBy ιK ιH := fun h =>
  have := h.isMulTorsionFree
  let ⟨k, hk⟩ := exists_ne (1 : K)
  not_isOfFinOrder_of_isMulTorsionFree hk (isOfFinOrder_of_finite k)

/-- The group `ℤ/2` is not separated by `ℤ`, with trivial coefficients: `ℤ` is torsion-free and
`ℤ/2` is a nontrivial finite group. -/
theorem not_isSeparatedBy_zmod_two_int :
    ¬IsSeparatedBy (1 : Unit →* Multiplicative (ZMod 2)) (1 : Unit →* Multiplicative ℤ) :=
  not_isSeparatedBy_of_finite _ _

/-- The direct product of a nonabelian group `K` and a nontrivial group `L` is not discriminated
by a commutative transitive group `H`, such as a free group, whatever the coefficients: `K × L`
is not commutative transitive. -/
theorem not_isDiscriminatedBy_prod_of_nontrivial [Nontrivial L] (hK : ¬IsMulCommutative K)
    (hH : Group.IsCommTransitive H) (ι : G →* K × L) (ιH : G →* H) : ¬IsDiscriminatedBy ι ιH :=
  fun h => Group.not_isCommTransitive_prod_of_nontrivial hK (h.isCommTransitive hH)

/-- `F₂ × F₂` is separated by `F₂`, with trivial coefficients, through the two projections. -/
theorem isSeparatedBy_freeGroup_prod_freeGroup :
    IsSeparatedBy (1 : Unit →* FreeGroup (Fin 2) × FreeGroup (Fin 2))
      (1 : Unit →* FreeGroup (Fin 2)) := by
  have h := (IsDiscriminatedBy.self (1 : Unit →* FreeGroup (Fin 2))).isSeparatedBy
  -- `IsSeparatedBy.prod` gives coefficients `MonoidHom.prod 1 1`, the only map out of `Unit`.
  simpa only [Subsingleton.elim ((1 : Unit →* FreeGroup (Fin 2)).prod 1) 1] using h.prod h

/-- `F₂ × F₂` is not discriminated by `F₂`, with trivial coefficients. Together with
`isSeparatedBy_freeGroup_prod_freeGroup` this shows that separation does not imply
discrimination. -/
theorem not_isDiscriminatedBy_freeGroup_prod_freeGroup :
    ¬IsDiscriminatedBy (1 : Unit →* FreeGroup (Fin 2) × FreeGroup (Fin 2))
      (1 : Unit →* FreeGroup (Fin 2)) :=
  not_isDiscriminatedBy_prod_of_nontrivial
    (FreeGroup.isMulCommutative_iff_subsingleton.not.2 (not_subsingleton _))
    IsFreeGroup.isCommTransitive _ _

/-- Separation by `H` is equivalent to triviality of the intersection of kernels of all
coefficient-preserving homomorphisms to `H`. -/
theorem isSeparatedBy_iff_iInf_ker (ιK : G →* K) (ιH : G →* H) :
    IsSeparatedBy ιK ιH ↔
      (⨅ φ : GHom ιK ιH, (φ : K →* H).ker) = ⊥ := by
  simp only [IsSeparatedBy, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf,
    MonoidHom.mem_ker]
  exact ⟨fun h k hk => by
      by_contra hne
      obtain ⟨φ, hφ⟩ := h k hne
      exact hφ (hk φ),
    fun h k hk => by
      by_contra hall
      apply hk
      apply h k
      intro φ
      by_contra hne
      exact hall ⟨φ, hne⟩⟩

end TauCeti.GroupAlgGeom
