/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Module.Submodule.EqLocus
import TauCeti.LinearAlgebra.Trace.Exact
import TauCeti.RepresentationTheory.Coset

/-!
# The subspace on which a representation acts through a character

For a representation `ρ` of a monoid `G` on `V` and a character `c : G →* k`, the vectors `v` with
`ρ g v = c g • v` for every `g` form a `G`-stable subspace `ρ.weightSpace c`, the intersection of
the eigenspaces of the `ρ g` for the eigenvalues `c g`. For `c = 1` it is the subspace of
invariants.
The name follows Mathlib's `LieModule.weightSpace`, the same intersection of eigenspaces for a Lie
module. `TauCeti.weightSpace` is the analogous space for the diagonal torus of a representation of
`GL n k`, indexed by integer weights.

Over a field, with `V` finite-dimensional, the trace of `ρ g` splits along this subspace as
`dim (ρ.weightSpace c) * c g` plus the trace of the induced action on the quotient.

Let `red : G →* Q` be a reduction homomorphism, `H ≤ Q` a subgroup, and `χ` a scalar
character of `H`. The weight space for the restriction to `red⁻¹(H)` and the pullback of `χ`
consists of the vectors on which each element above `H` acts by the character of its reduction.

If inverse conjugation by an element of `Q` preserves `H` and `χ`, every lift induces the same
endomorphism of this weight space. A monoid mapping into these elements acts on the weight space
provided each element of its image lifts through `red`. The resulting representation is
`Representation.weightSpaceLift`.

## Main definitions

* `Representation.weightSpace ρ c`: the vectors on which `G` acts through `c`.
* `Representation.weightSpaceLift`: the action by lifts on the pulled-back weight space.

## Main results

* `Representation.mem_weightSpace`: membership is the equation `ρ g v = c g • v` for every `g`.
* `Representation.weightSpace_one`: for a group `G`, the trivial character cuts out the invariants.
* `Representation.weightSpace_le_comap`: `ρ.weightSpace c` is `G`-stable.
* `Representation.trace_eq_finrank_weightSpace_mul_add`: the splitting of the trace.
* `Representation.mem_weightSpace_comp_subgroupComap_iff`: membership in the
  pulled-back weight space in terms of arbitrary lifts.

## References

The lift action and its two supporting lemmas generalize `New.levelRep`,
`New.apply_liftResidue_eq`, and `New.map_liftResidue_mem_levelSpace` in the `rh-new`
development (`src/Lib/Adelic/Unitary/CongruenceLevels.lean`).
-/

public section

open Module

namespace Representation

section Basic

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The vectors on which the representation `ρ` acts through the character `c`. -/
def weightSpace (ρ : Representation k G V) (c : G →* k) : Submodule k V :=
  ⨅ g, (ρ g).eqLocus (c g • LinearMap.id)

/-- Membership in a weight space means every monoid element acts by its character value. -/
@[simp]
theorem mem_weightSpace {ρ : Representation k G V} {c : G →* k} {v : V} :
    v ∈ ρ.weightSpace c ↔ ∀ g, ρ g v = c g • v := by
  simp [weightSpace]

/-- For a group, the subspace on which `ρ` acts through the trivial character is the subspace of
invariants. -/
@[simp]
theorem weightSpace_one {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    ρ.weightSpace 1 = ρ.invariants := by
  ext
  simp

/-- The subspace on which `ρ` acts through a character is `G`-stable. -/
theorem weightSpace_le_comap (ρ : Representation k G V) (c : G →* k) (h : G) :
    ρ.weightSpace c ≤ (ρ.weightSpace c).comap (ρ h) := by
  intro v hv
  rw [Submodule.mem_comap, mem_weightSpace]
  rw [mem_weightSpace] at hv
  intro g
  rw [← mul_apply_eq_comp, ← map_mul, hv, hv, map_mul, mul_smul]

/-- The trace of `ρ g` splits along the vectors on which `G` acts through `c`. -/
theorem trace_eq_finrank_weightSpace_mul_add {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V]
    [FiniteDimensional F V] (ρ : Representation F G V) (c : G →* F) (g : G) :
    LinearMap.trace F V (ρ g) = finrank F (ρ.weightSpace c) * c g +
      LinearMap.trace F _ (ρ.quotient _ (weightSpace_le_comap ρ c) g) := by
  have hU (v) (hv : v ∈ ρ.weightSpace c) : ρ g v ∈ ρ.weightSpace c := weightSpace_le_comap ρ c g hv
  have hres : (ρ g).restrict hU = c g • LinearMap.id := by
    ext ⟨v, hv⟩
    simp [LinearMap.restrict_apply, (mem_weightSpace.mp hv) g]
  rw [LinearMap.trace_eq_add_of_exact (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) (fN := (ρ g).restrict hU)
    (fQ := ρ.quotient _ (weightSpace_le_comap ρ c) g) (by ext; simp) (by ext; simp), hres,
    map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

end Basic

section Reduction

variable {k V G Q S : Type*} [CommSemiring k] [AddCommMonoid V] [Module k V]
  [Group G] [Group Q] [Monoid S]

variable (ρ : Representation k G V) (red : G →* Q) {H : Subgroup Q} (χ : H →* k)

/-- Membership in the pulled-back weight space means every lift of an element of the
subgroup acts by the character of its reduction. -/
theorem mem_weightSpace_comp_subgroupComap_iff {v : V} :
    v ∈ weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H)) ↔
      ∀ (b : G) (h : H), red b = h → ρ b v = χ h • v := by
  rw [mem_weightSpace]
  constructor
  · intro hv b h hb
    let b' : H.comap red := ⟨b, Subgroup.mem_comap.mpr (hb ▸ h.property)⟩
    have hb' : red.subgroupComap H b' = h := by
      apply Subtype.ext
      exact (MonoidHom.subgroupComap_apply_coe red H b').trans hb
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, hb'] using hv b'
  · intro hv b
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using
      hv b (red.subgroupComap H b) (MonoidHom.subgroupComap_apply_coe red H b).symm

/-- On the pulled-back weight space, a lift acts by the character of its reduction. -/
theorem apply_eq_smul_of_mem_weightSpace_of_map_eq {v : V}
    (hv : v ∈ weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H)))
    {b : G} {h : H} (hb : red b = h) : ρ b v = χ h • v :=
  (ρ.mem_weightSpace_comp_subgroupComap_iff red χ).mp hv b h hb

/-- Two elements with the same reduction have the same action on the pulled-back weight space. -/
theorem apply_eq_apply_of_mem_weightSpace_of_map_eq {v : V}
    (hv : v ∈ weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H)))
    {g g' : G} (heq : red g = red g') : ρ g v = ρ g' v := by
  have hfix (b : red.ker) : ρ b v = v := by
    simpa only [map_one, one_smul] using
      ρ.apply_eq_smul_of_mem_weightSpace_of_map_eq red χ hv (h := 1)
        (MonoidHom.mem_ker.mp b.property)
  exact ρ.apply_eq_apply_of_quotientGroup_mk_eq hfix
    (QuotientGroup.eq.mpr (by simp [MonoidHom.mem_ker, heq]))

/-- A lift preserves the pulled-back weight space if inverse conjugation by its reduction
preserves the subgroup and its character. -/
theorem apply_mem_weightSpace_comp_subgroupComap {g : G}
    (hg : ∀ h : H, ∃ h' : H, (red g)⁻¹ * h * red g = h' ∧ χ h' = χ h)
    {v : V}
    (hv : v ∈ weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H))) :
    ρ g v ∈ weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H)) := by
  rw [mem_weightSpace]
  intro b
  obtain ⟨h', hconj, hchar⟩ := hg (red.subgroupComap H b)
  have hred : red (g⁻¹ * b * g) = h' := by
    rw [map_mul, map_mul, map_inv]
    exact hconj
  have hfix := ρ.apply_eq_smul_of_mem_weightSpace_of_map_eq red χ hv hred
  calc
    ρ b (ρ g v) = ρ (b * g) v := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ (g * (g⁻¹ * b * g)) v := by simp [← mul_assoc]
    _ = ρ g (ρ (g⁻¹ * b * g) v) := by rw [map_mul, mul_apply_eq_comp]
    _ = χ (red.subgroupComap H b) • ρ g v := by rw [hfix, hchar, map_smul]

variable (φ : S →* Q)
  (hlift : ∀ s, ∃ g, red g = φ s)
  (hχ : ∀ (s : S) (h : H), ∃ h' : H, (φ s)⁻¹ * h * φ s = h' ∧ χ h' = χ h)

private noncomputable def chooseLift (s : S) : G :=
  (hlift s).choose

@[simp]
private theorem map_chooseLift (s : S) : red (chooseLift red φ hlift s) = φ s :=
  (hlift s).choose_spec

/-- A monoid homomorphism acts on the pulled-back weight space by lifts through reduction
when each image element lifts and its inverse conjugation preserves the subgroup and character. -/
noncomputable def weightSpaceLift :
    Representation k S (weightSpace (ρ.comp (H.comap red).subtype)
      (χ.comp (red.subgroupComap H))) where
  toFun s := (ρ (chooseLift red φ hlift s)).restrict fun _ hv ↦
    ρ.apply_mem_weightSpace_comp_subgroupComap red χ
      (by simpa only [map_chooseLift] using hχ s) hv
  map_one' := by
    ext v
    simp only [LinearMap.coe_restrict_apply, one_apply_eq_self]
    calc
      _ = ρ 1 v := ρ.apply_eq_apply_of_mem_weightSpace_of_map_eq red χ v.property (by simp)
      _ = _ := by simp
  map_mul' s t := by
    ext v
    simp only [LinearMap.coe_restrict_apply, mul_apply_eq_comp]
    rw [← mul_apply_eq_comp, ← map_mul]
    exact ρ.apply_eq_apply_of_mem_weightSpace_of_map_eq red χ v.property (by simp)

/-- Evaluate `weightSpaceLift` using any lift of the given element. -/
theorem weightSpaceLift_apply (s : S)
    (v : weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H))) {g : G}
    (hg : red g = φ s) : (ρ.weightSpaceLift red χ φ hlift hχ s v : V) = ρ g v :=
  ρ.apply_eq_apply_of_mem_weightSpace_of_map_eq red χ v.property
    ((map_chooseLift red φ hlift s).trans hg.symm)

end Reduction

end Representation
