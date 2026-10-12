/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.ProjectiveExtension
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.SchurMultiplier
import TauCeti.RepresentationTheory.Irreducible

/-!
# The Clifford obstruction

Let `N` be a normal subgroup of `G`, let `A` be an irreducible finite-dimensional representation of
`N` over an algebraically closed field `k`, and let `T = inertia A` be its inertia group. Whether
`A` extends to an ordinary representation of `T` is governed by a class in the Schur multiplier
`H²(T/N, kˣ)` of the *quotient* `T/N`, the **Clifford obstruction** `TauCeti.cliffordObstruction A`.

The class comes from a projective extension of `A` to `T` chosen compatibly with `N`
(`TauCeti.IsProjectiveInertiaExtension`): a projective representation `ρ` of `T` on `A` that agrees
with `A` on `N` and whose factor set is inflated from a factor set `β` on `T/N`. Such an extension
exists (`TauCeti.exists_isProjectiveInertiaExtension`): starting from any projective extension
implementing conjugation on `N`, redefine it on each coset `tN` from its value at a chosen coset
representative, so that `ρ (t * n) = ρ t ∘ A n`. The factor set is then trivial whenever one of its
arguments lies in `N`, and so descends to `T/N` (`TauCeti.IsFactorSet.exists_eq_apply_mk`).

The extension is not unique, but its class is
(`TauCeti.IsProjectiveInertiaExtension.cohomologyClass_factorSet_eq`): by Schur's lemma two such
extensions differ by scalars, which are constant on the cosets of `N`, so the two factor sets on
`T/N` differ by a coboundary. The Clifford obstruction is the common class, and it vanishes exactly
when `A` extends to a representation of its inertia group
(`TauCeti.cliffordObstruction_eq_zero_iff`).

## Main definitions

* `TauCeti.IsProjectiveInertiaExtension A ρ β`: `ρ` is a projective representation of
  `inertia A` on `A` that restricts to `A` on `N` and whose factor set is inflated from `β`.
* `TauCeti.IsProjectiveInertiaExtension.factorSet`: the factor set `β` on the inertia quotient,
  bundled as a `TauCeti.FactorSet`.
* `TauCeti.cliffordObstruction A`: the Clifford obstruction in `H²(inertia A ⧸ N, kˣ)`.

## Main results

* `TauCeti.exists_isProjectiveInertiaExtension`: a compatible projective extension exists.
* `TauCeti.IsProjectiveInertiaExtension.apply_apply_conjNormal`: its operators implement
  conjugation on `N`.
* `TauCeti.IsProjectiveInertiaExtension.cohomologyClass_factorSet_eq`: any two compatible projective
  extensions have the same class, and
  `TauCeti.IsProjectiveInertiaExtension.cohomologyClass_factorSet_eq_cliffordObstruction`: that
  class is the Clifford obstruction.
* `TauCeti.cliffordObstruction_eq_zero_iff`: **`A` extends to a representation of its inertia
  group if and only if its Clifford obstruction vanishes.**

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 11
  (Theorems 11.2 and 11.7).
* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace TauCeti

open CategoryTheory _root_.Representation

universe u v

section Extension

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {N : Subgroup G} [N.Normal]
  (A : FDRep k N)

/-- An element of `N` is trivial in the inertia quotient. -/
private theorem mk_inclusion_eq_one (n : N) :
    ((Subgroup.inclusion (le_inertia A) n : inertia A) : inertia A ⧸ N.subgroupOf (inertia A))
      = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 n.2)

/-- **A projective extension of `A` to its inertia group, compatible with `N`**: a projective
representation `ρ` of `inertia A` on `A` that restricts to `A` on `N` and whose factor set is
inflated from the factor set `β` on the inertia quotient `inertia A ⧸ N`. Its operators implement
conjugation on `N` (`TauCeti.IsProjectiveInertiaExtension.apply_apply_conjNormal`), and the class
of `β` is the Clifford obstruction of `A`
(`TauCeti.IsProjectiveInertiaExtension.cohomologyClass_factorSet_eq_cliffordObstruction`). -/
structure IsProjectiveInertiaExtension (ρ : inertia A → A ≃ₗ[k] A)
    (β : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ) :
    Prop where
  /-- `ρ` is a projective representation whose factor set is inflated from `β`. -/
  isProjectiveRep : IsProjectiveRep ρ fun s t ↦ β s t
  /-- `ρ` restricts to `A` on `N`. -/
  apply_inclusion (n : N) (x : A) : ρ (Subgroup.inclusion (le_inertia A) n) x = A.ρ n x

namespace IsProjectiveInertiaExtension

variable {A} {ρ : inertia A → A ≃ₗ[k] A}
  {β : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ}
  (h : IsProjectiveInertiaExtension A ρ β)
include h

/-- The factor set on the inertia quotient is a normalized factor set. -/
theorem isFactorSet : IsFactorSet β :=
  IsFactorSet.of_comp (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    h.isProjectiveRep.isFactorSet

/-- Multiplying on the right by an element of `N` composes with its action. -/
theorem apply_mul_inclusion (t : inertia A) (n : N) (x : A) :
    ρ (t * Subgroup.inclusion (le_inertia A) n) x = ρ t (A.ρ n x) := by
  have hmul := h.isProjectiveRep.mul_apply t (Subgroup.inclusion (le_inertia A) n) x
  rw [h.apply_inclusion, mk_inclusion_eq_one, h.isFactorSet.one_right] at hmul
  simpa using hmul.symm

/-- Multiplying on the left by an element of `N` composes with its action. -/
theorem apply_inclusion_mul (n : N) (t : inertia A) (x : A) :
    ρ (Subgroup.inclusion (le_inertia A) n * t) x = A.ρ n (ρ t x) := by
  have hmul := h.isProjectiveRep.mul_apply (Subgroup.inclusion (le_inertia A) n) t x
  rw [h.apply_inclusion, mk_inclusion_eq_one, h.isFactorSet.one_left] at hmul
  simpa using hmul.symm

/-- **The operators of a compatible projective extension implement conjugation on `N`**:
`ρ t ∘ A n = A (t n t⁻¹) ∘ ρ t`. -/
theorem apply_apply_conjNormal (t : inertia A) (n : N) (x : A) :
    ρ t (A.ρ n x) = A.ρ (MulAut.conjNormal (t : G) n) (ρ t x) := by
  rw [← h.apply_mul_inclusion, ← h.apply_inclusion_mul]
  congr 2
  ext
  simp [mul_assoc]

section TrivialAction

attribute [local instance] trivialMulDistribMulAction

omit h in
/-- The factor set on the inertia quotient of a compatible projective extension, bundled as a
`TauCeti.FactorSet` for the trivial action of the quotient on `kˣ`. -/
noncomputable def factorSet (h : IsProjectiveInertiaExtension A ρ β) :
    FactorSet (inertia A ⧸ N.subgroupOf (inertia A)) kˣ :=
  letI := h.isFactorSet
  IsFactorSet.toFactorSet β trivialMulDistribMulAction_smul

@[simp]
theorem factorSet_apply (p : (inertia A ⧸ N.subgroupOf (inertia A)) × _) :
    h.factorSet p = β p.1 p.2 :=
  letI := h.isFactorSet
  IsFactorSet.toFactorSet_apply β trivialMulDistribMulAction_smul p

end TrivialAction

end IsProjectiveInertiaExtension

end Extension

section Existence

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] {N : Subgroup G}
  [N.Normal] (A : FDRep k N) [Simple A]

/-- **An irreducible representation of a normal subgroup extends to a compatible projective
representation of its inertia group** over an algebraically closed field: one that agrees with
`A` on `N` and whose factor set is inflated from the inertia quotient. -/
theorem exists_isProjectiveInertiaExtension :
    ∃ ρ β, IsProjectiveInertiaExtension A ρ β := by
  classical
  have : Nontrivial A := (FDRep.isIrreducible_of_simple A).nontrivial
  set M := N.subgroupOf (inertia A)
  set ι : N →* inertia A := Subgroup.inclusion (le_inertia A) with hι
  have hιM (n : N) : ι n ∈ M := Subgroup.mem_subgroupOf.2 n.2
  obtain ⟨ρ₀, -, -, hres, hinter⟩ := exists_isProjectiveRep_inertia_restrict_eq A
  -- `Subgroup.inclusion` sends `n` to `⟨n, _⟩` by definition, the form in which `hres` is stated.
  have hres' (n : N) (x : A) : ρ₀ (ι n) x = A.ρ n x := hres n x
  -- Fix a representative `s t` of each coset `tN`; then `t = s t * m t` with `m t ∈ N`.
  obtain ⟨s, hs, hsmul⟩ : ∃ s : inertia A → inertia A,
      (∀ t, (s t)⁻¹ * t ∈ M) ∧ ∀ t, ∀ n ∈ M, s (t * n) = s t :=
    ⟨fun t ↦ (t : inertia A ⧸ M).out, fun t ↦ QuotientGroup.eq.1 (QuotientGroup.out_eq' _),
      fun t n hn ↦ by simp only [QuotientGroup.mk_mul_of_mem t hn]⟩
  obtain ⟨m, hm⟩ : ∃ m : inertia A → N, ∀ t, (m t : G) = (((s t)⁻¹ * t : inertia A) : G) :=
    ⟨fun t ↦ ⟨_, Subgroup.mem_subgroupOf.1 (hs t)⟩, fun _ ↦ rfl⟩
  -- The new extension acts on `tN` through its representative: `ρ t = ρ₀ (s t) ∘ A (m t)`.
  let r : N →* (A ≃ₗ[k] A) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k A).toMonoidHom.comp A.ρ.toHomUnits
  obtain ⟨ρ, hρ⟩ : ∃ ρ : inertia A → A ≃ₗ[k] A, ∀ t x, ρ t x = ρ₀ (s t) (A.ρ (m t) x) :=
    ⟨fun t ↦ (r (m t)).trans (ρ₀ (s t)), fun t x ↦ by simp [r]⟩
  have hρ1 : ρ 1 = 1 := by
    refine LinearEquiv.ext fun x ↦ ?_
    have hs1 : ((s 1 : inertia A) : G) ∈ N := Subgroup.mem_subgroupOf.1 (by simpa using hs 1)
    obtain ⟨u, hu⟩ : ∃ u : N, ι u = s 1 := ⟨⟨_, hs1⟩, Subtype.ext rfl⟩
    have hmu : m 1 = u⁻¹ := Subtype.ext (by simp [hm, ← hu, hι])
    rw [hρ, hmu, ← hu, hres', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hρmul (t : inertia A) (n : N) (x : A) : ρ (t * ι n) x = ρ t (A.ρ n x) := by
    have hst : s (t * ι n) = s t := hsmul t _ (hιM n)
    have hmt : m (t * ι n) = m t * n := Subtype.ext (by
      rw [hm, hst]
      simp [hm, hι, mul_assoc])
    rw [hρ, hρ, hst, hmt, map_mul, Module.End.mul_apply]
  have hρι (n : N) (x : A) : ρ (ι n) x = A.ρ n x := by
    simpa [hρ1] using hρmul 1 n x
  have hρconj (t : inertia A) (n : N) (x : A) :
      ρ t (A.ρ n x) = A.ρ (MulAut.conjNormal (t : G) n) (ρ t x) := by
    have hconj : MulAut.conjNormal (t : G) n
        = MulAut.conjNormal (s t : G) (m t * n * (m t)⁻¹) :=
      Subtype.ext (by simp [hm, mul_assoc])
    rw [hρ, hρ, hconj, ← hinter]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel_right]
  have hιmul (n : N) (t : inertia A) (x : A) : ρ (ι n * t) x = A.ρ n (ρ t x) := by
    have hn : ι n * t = t * ι (MulAut.conjNormal ((t : G)⁻¹) n) :=
      Subtype.ext (by simp [hι, mul_assoc])
    have hc : MulAut.conjNormal (t : G) (MulAut.conjNormal ((t : G)⁻¹) n) = n := by
      simp
    rw [hn, hρmul, hρconj, hc]
  -- By Schur's lemma `ρ` is a projective representation.
  obtain ⟨α, hproj⟩ := exists_isProjectiveRep_of_apply_apply_conjNormal A hρ1 hρconj
  -- Its factor set is trivial as soon as one argument lies in `N`, so it descends to `T/N`.
  have hone (a : kˣ) (t : inertia A) (ha : ∀ x, (a : k) • ρ t x = ρ t x) : a = 1 := by
    refine FaithfulSMul.eq_of_smul_eq_smul (α := A) fun y ↦ ?_
    obtain ⟨x, rfl⟩ := (ρ t).surjective y
    simpa [Units.smul_def] using ha x
  have hαr (t : inertia A) (a : inertia A) (ha : a ∈ M) : α t a = 1 := by
    obtain ⟨n, rfl⟩ : ∃ n : N, ι n = a := ⟨⟨_, Subgroup.mem_subgroupOf.1 ha⟩, Subtype.ext rfl⟩
    refine hone _ (t * ι n) fun x ↦ ?_
    rw [← hproj.mul_apply, hρι, hρmul]
  have hαl (t : inertia A) (a : inertia A) (ha : a ∈ M) : α a t = 1 := by
    obtain ⟨n, rfl⟩ : ∃ n : N, ι n = a := ⟨⟨_, Subgroup.mem_subgroupOf.1 ha⟩, Subtype.ext rfl⟩
    refine hone _ (ι n * t) fun x ↦ ?_
    rw [← hproj.mul_apply, hρι, hιmul]
  have := hproj.isFactorSet
  obtain ⟨β, -, hβ⟩ := IsFactorSet.exists_eq_apply_mk (N := M) hαr hαl
  have hαβ : α = fun s t : inertia A ↦ β s t := funext fun s ↦ funext fun t ↦ hβ s t
  exact ⟨ρ, β, hαβ ▸ hproj, hρι⟩

end Existence

section Obstruction

attribute [local instance] trivialMulDistribMulAction

variable {k G : Type} [Field k] [IsAlgClosed k] [Group G] {N : Subgroup G} [N.Normal]
  {A : FDRep k N} [Simple A]

namespace IsProjectiveInertiaExtension

variable {ρ ρ' : inertia A → A ≃ₗ[k] A}
  {β β' : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ}

/-- **Any two compatible projective extensions of `A` to its inertia group have the same class in
the Schur multiplier of the inertia quotient.** -/
theorem cohomologyClass_factorSet_eq (h : IsProjectiveInertiaExtension A ρ β)
    (h' : IsProjectiveInertiaExtension A ρ' β') :
    h'.factorSet.cohomologyClass = h.factorSet.cohomologyClass := by
  have hA := FDRep.isIrreducible_of_simple A
  have : Nontrivial A := hA.nontrivial
  set ι : N →* inertia A := Subgroup.inclusion (le_inertia A)
  -- The two extensions differ by scalars, by Schur's lemma.
  have hc (t : inertia A) : ∃ c : kˣ, ∀ x, ρ' t x = (c : k) • ρ t x :=
    IsIrreducible.exists_unit_smul_of_intertwines
      (σ := A.ρ.comp (MulAut.conjNormal (t : G)).toMonoidHom) (ρ' t) (ρ t)
      (h'.apply_apply_conjNormal t) (h.apply_apply_conjNormal t)
  choose c hc using hc
  have hone (a b : kˣ) (t : inertia A) (hab : ∀ x, (a : k) • ρ t x = (b : k) • ρ t x) :
      a = b := by
    refine FaithfulSMul.eq_of_smul_eq_smul (α := A) fun y ↦ ?_
    obtain ⟨x, rfl⟩ := (ρ t).surjective y
    simpa [Units.smul_def] using hab x
  -- The scalars are constant on the cosets of `N`, so they descend to the quotient.
  have hcN (t : inertia A) (n : N) : c (t * ι n) = c t :=
    hone _ _ (t * ι n) fun x ↦ by
      rw [← hc, h'.apply_mul_inclusion, hc, h.apply_mul_inclusion]
  have hcM (a b : inertia A) (hab : QuotientGroup.leftRel (N.subgroupOf (inertia A)) a b) :
      c a = c b := by
    rw [QuotientGroup.leftRel_apply] at hab
    obtain ⟨n, hn⟩ : ∃ n : N, ι n = a⁻¹ * b :=
      ⟨⟨_, Subgroup.mem_subgroupOf.1 hab⟩, Subtype.ext rfl⟩
    rw [← mul_inv_cancel_left a b, ← hn, hcN]
  let d : inertia A ⧸ N.subgroupOf (inertia A) → kˣ := Quotient.lift c hcM
  have hd (t : inertia A) : d t = c t := rfl
  -- The scalars relate the two factor sets.
  have hkey (s t : inertia A) : β' s t * c (s * t) = c s * c t * β s t := by
    refine hone _ _ (s * t) fun x ↦ ?_
    have h₁ := h'.isProjectiveRep.mul_apply s t x
    rw [hc s, hc t, hc (s * t), map_smul, h.isProjectiveRep.mul_apply] at h₁
    simpa only [Units.val_mul, mul_smul] using h₁.symm
  refine (FactorSet.cohomologyClass_eq_iff _ _).2 ⟨d, fun q₁ q₂ ↦ ?_⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q₂
  simp only [trivialMulDistribMulAction_smul, factorSet_apply, ← QuotientGroup.mk_mul, hd]
  rw [eq_div_of_mul_eq' (hkey s t)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

end IsProjectiveInertiaExtension

variable (A) in
/-- **The Clifford obstruction** of an irreducible representation `A` of a normal subgroup `N`: the
class in the Schur multiplier `H²(inertia A ⧸ N, kˣ)` of the factor set of any compatible projective
extension of `A` to its inertia group (`TauCeti.IsProjectiveInertiaExtension`). It does not depend
on the extension
(`TauCeti.IsProjectiveInertiaExtension.cohomologyClass_factorSet_eq_cliffordObstruction`), and it
vanishes exactly when `A` extends to a representation of its inertia group
(`TauCeti.cliffordObstruction_eq_zero_iff`). -/
noncomputable def cliffordObstruction :
    schurMultiplier k (inertia A ⧸ N.subgroupOf (inertia A)) :=
  (exists_isProjectiveInertiaExtension A).choose_spec.choose_spec.factorSet.cohomologyClass

/-- **The Clifford obstruction is the class of every compatible projective extension.** -/
theorem IsProjectiveInertiaExtension.cohomologyClass_factorSet_eq_cliffordObstruction
    {ρ : inertia A → A ≃ₗ[k] A}
    {β : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ}
    (h : IsProjectiveInertiaExtension A ρ β) :
    h.factorSet.cohomologyClass = cliffordObstruction A :=
  (exists_isProjectiveInertiaExtension A).choose_spec.choose_spec.cohomologyClass_factorSet_eq h

/-- **An irreducible representation of a normal subgroup extends to a representation of its
inertia group exactly when its Clifford obstruction vanishes.** -/
theorem cliffordObstruction_eq_zero_iff :
    cliffordObstruction A = 0 ↔
      ∃ σ : Representation k (inertia A) A, σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ := by
  obtain ⟨ρ, β, h⟩ := exists_isProjectiveInertiaExtension A
  rw [← h.cohomologyClass_factorSet_eq_cliffordObstruction]
  constructor
  · intro h0
    -- The factor set on the quotient is a coboundary; rescaling `ρ` by it linearizes `ρ`.
    obtain ⟨x, hx⟩ := (FactorSet.cohomologyClass_eq_zero_iff _).1 h0
    simp only [trivialMulDistribMulAction_smul, IsProjectiveInertiaExtension.factorSet_apply]
      at hx
    have hx1 : x 1 = 1 := by
      simpa [h.isFactorSet.one_left] using hx 1 1
    have hrs := h.isProjectiveRep.rescale (fun t ↦ (x t)⁻¹) (by simp [hx1])
    have hrs' : IsProjectiveRep (fun t ↦ (ρ t).trans (LinearEquiv.smulOfUnit (x t)⁻¹)) 1 := by
      convert hrs using 1
      funext s t
      rw [Pi.one_apply, Pi.one_apply, ← hx, QuotientGroup.mk_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    refine ⟨LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp hrs'.toMonoidHom, ?_⟩
    ext n y
    simp [mk_inclusion_eq_one, hx1, h.apply_inclusion]
  · rintro ⟨σ, hσ⟩
    let π : inertia A →* (A ≃ₗ[k] A) :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k A).toMonoidHom.comp σ.toHomUnits
    have hπ : IsProjectiveInertiaExtension A π 1 :=
      ⟨IsProjectiveRep.of_monoidHom π, fun n x ↦ by simp [π, ← hσ]⟩
    have htriv : hπ.factorSet = FactorSet.trivial _ _ := FactorSet.ext fun _ ↦ by simp
    rw [hπ.cohomologyClass_factorSet_eq h, htriv]
    exact FactorSet.cohomologyClass_trivial

end Obstruction

end TauCeti
