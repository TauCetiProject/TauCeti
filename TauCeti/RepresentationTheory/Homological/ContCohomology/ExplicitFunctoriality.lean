/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Equiv
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Functoriality of explicit continuous cohomology in degrees one and two

A compatible pair consists of a continuous monoid homomorphism `φ : H →ₜ* G` and a continuous
additive homomorphism `f : M →+ N` satisfying
`f (φ h • m) = h • f m`. It pulls a continuous cochain `c : G → M` back to
`h ↦ f (c (φ h))`. This file proves that pullback preserves continuous cocycles and
coboundaries, and descends it to the explicit groups `H¹ = Z¹/B¹` and `H² = Z²/B²`.

The resulting maps are `TauCeti.ContCohomology.explicitMap1` and `explicitMap2`. Their identity
and composition laws make the construction functorial, while the `_mk` theorems fix
their values on cocycle classes. The named specializations `explicitRes1`, `explicitRes2`,
`explicitCoeff1`, and `explicitCoeff2` provide restriction and coefficient maps in positive
degrees, and `explicitRes1_eq_explicitMap1`, `explicitRes2_eq_explicitMap2`,
`explicitCoeff1_eq_explicitMap1` and `explicitCoeff2_eq_explicitMap2` exhibit each of them as the
compatible pair it is, so that a theorem proved for a general pair specializes to all four. They
are the positive-degree counterparts of `explicitRes0_eq_explicitMap0` and
`explicitCoeff0_eq_explicitMap0`. The constructions `explicitCoeff1Equiv` and
`explicitCoeff2Equiv` upgrade a continuous equivariant additive equivalence of coefficient modules
to additive equivalences on explicit `H¹` and `H²`, and `explicitCoeff1_bijective` and
`explicitCoeff2_bijective` record that a bijective equivariant homomorphism of discrete coefficient
modules induces bijections. Finally, `explicitCoeff2_eq_card_nsmul` records that the norm of a
finite normal subgroup `N`, as a coefficient map, acts on `H²` as multiplication by `#N`.

This is functoriality of the *explicit* model: the carriers are the quotients `Z¹/B¹` and `Z²/B²`
of plain continuous cochains. Mathlib's `ContinuousCohomology.map` is the compatible-pair pullback
on the canonical bundled carrier, and it is what the sibling file
`TauCeti/RepresentationTheory/Homological/ContCohomology/Functoriality.lean` specialises to
restriction, inflation and coefficient maps. The comparison with the canonical model lives in
`TauCeti/RepresentationTheory/Homological/ContCohomology/CohomologyComparison.lean`.

The formulas follow Mathlib's `groupCohomology.cochainsMap₁`, `cochainsMap₂`, `mapCocycles₁`, and
`mapCocycles₂`, with universe-polymorphic unbundled continuous coefficients. The coefficient maps
and their equivalences apply to monoid actions; restriction to subgroups requires a group.
-/

public section

namespace TauCeti.ContCohomology

universe uG uH uM uN uK uP

section Cochains

variable {G : Type uG} {H : Type uH} {M : Type uM} {N : Type uN}
  [Monoid G] [Monoid H] [AddMonoid M] [AddMonoid N]

/-- Pullback of degree-one cochains along a monoid map and a coefficient map. -/
def cochainsMap1 (φ : H →* G) (f : M →+ N) : (G → M) →+ (H → N) where
  toFun c h := f (c (φ h))
  map_zero' := by
    ext h
    simp
  map_add' c d := by
    ext h
    simp

/-- Pullback of degree-two cochains along a monoid map and a coefficient map: the degree-one
pullback along the pair `φ × φ` of the domain. -/
def cochainsMap2 (φ : H →* G) (f : M →+ N) : (G × G → M) →+ (H × H → N) :=
  cochainsMap1 (φ.prodMap φ) f

/-- The defining formula for the degree-one cochain pullback. -/
@[simp]
theorem cochainsMap1_apply (φ : H →* G) (f : M →+ N) (c : G → M) (h : H) :
    cochainsMap1 φ f c h = f (c (φ h)) :=
  by rfl

/-- The defining formula for the degree-two cochain pullback. -/
@[simp]
theorem cochainsMap2_apply (φ : H →* G) (f : M →+ N) (c : G × G → M) (h k : H) :
    cochainsMap2 φ f c (h, k) = f (c (φ h, φ k)) :=
  by rfl

/-- Pullback of degree-one cochains is injective when the group map is surjective and the
coefficient map is injective. -/
theorem cochainsMap1_injective (φ : H →* G) (f : M →+ N) (hφ : Function.Surjective φ)
    (hf : Function.Injective f) : Function.Injective (cochainsMap1 φ f) :=
  hφ.injective_comp_right.comp hf.comp_left

/-- Pullback of degree-two cochains is injective when the group map is surjective and the
coefficient map is injective. -/
theorem cochainsMap2_injective (φ : H →* G) (f : M →+ N) (hφ : Function.Surjective φ)
    (hf : Function.Injective f) : Function.Injective (cochainsMap2 φ f) :=
  cochainsMap1_injective (φ.prodMap φ) f (hφ.prodMap hφ) hf

/-- Pullback preserves continuity of degree-one cochains. -/
theorem continuous_cochainsMap1 [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace M] [TopologicalSpace N] (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    {c : G → M} (hc : Continuous c) : Continuous (cochainsMap1 (φ : H →* G) f c) :=
  hf.comp (hc.comp φ.continuous)

/-- Pullback preserves continuity of degree-two cochains. -/
theorem continuous_cochainsMap2 [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace M] [TopologicalSpace N] (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    {c : G × G → M} (hc : Continuous c) : Continuous (cochainsMap2 (φ : H →* G) f c) :=
  continuous_cochainsMap1 (φ.prodMap φ) f hf hc

/-- Pullback of degree-one cochains along the identity compatible pair is the identity. -/
@[simp]
theorem cochainsMap1_id :
    cochainsMap1 (MonoidHom.id G) (AddMonoidHom.id M) =
      AddMonoidHom.id (G → M) := by
  ext c g
  rfl

/-- Pullback of degree-two cochains along the identity compatible pair is the identity. -/
@[simp]
theorem cochainsMap2_id :
    cochainsMap2 (MonoidHom.id G) (AddMonoidHom.id M) =
      AddMonoidHom.id (G × G → M) :=
  cochainsMap1_id

/-- Pullback of degree-one cochains along a composite compatible pair is the composite of the
pullbacks: it is contravariant in the group homomorphism and covariant in the coefficient map. -/
@[simp]
theorem cochainsMap1_comp {K : Type uK} {P : Type uP} [Monoid K] [AddMonoid P]
    (φ : H →* G) (ψ : K →* H) (f : M →+ N) (q : N →+ P) :
    cochainsMap1 (φ.comp ψ) (q.comp f) = (cochainsMap1 ψ q).comp (cochainsMap1 φ f) := by
  ext c k
  rfl

/-- Pullback of degree-two cochains along a composite compatible pair is the composite of the
pullbacks: it is contravariant in the group homomorphism and covariant in the coefficient map. -/
@[simp]
theorem cochainsMap2_comp {K : Type uK} {P : Type uP} [Monoid K] [AddMonoid P]
    (φ : H →* G) (ψ : K →* H) (f : M →+ N) (q : N →+ P) :
    cochainsMap2 (φ.comp ψ) (q.comp f) = (cochainsMap2 ψ q).comp (cochainsMap2 φ f) :=
  cochainsMap1_comp (φ.prodMap φ) (ψ.prodMap ψ) f q

end Cochains

section Naturality

/-! The naturality squares are where the differentials enter, so this is the first point at which
the coefficients have to be commutative groups carrying a distributive scalar action. Commutativity
is necessary because `d0` and `d1` are additive homomorphisms; their formulas are not additive for
a general noncommutative additive group. -/

variable {G : Type uG} {H : Type uH} {M : Type uM} {N : Type uN}
  [Monoid G] [Monoid H] [AddCommGroup M] [AddCommGroup N]
  [DistribSMul G M] [DistribSMul H N]

/-- The degree-zero differential is natural in compatible pairs. -/
theorem cochainsMap1_d0 (φ : H →* G) (f : M →+ N)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (m : M) :
    cochainsMap1 φ f (d0 G M m) = d0 H N (f m) := by
  ext h
  simp only [cochainsMap1_apply, d0_apply, map_sub, hequiv]

/-- The degree-one differential is natural in compatible pairs. -/
theorem cochainsMap2_d1 (φ : H →* G) (f : M →+ N)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : G → M) :
    cochainsMap2 φ f (d1 G M c) = d1 H N (cochainsMap1 φ f c) := by
  ext p
  obtain ⟨h, k⟩ := p
  simp only [cochainsMap2_apply, d1_apply, map_add, map_sub, hequiv, cochainsMap1_apply,
    map_mul]

/-- A compatible pair sends degree-one coboundaries to degree-one coboundaries. -/
theorem cochainsMap1_mem_B1 (φ : H →* G) (f : M →+ N)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    {c : G → M} (hc : c ∈ B1 G M) :
    cochainsMap1 φ f c ∈ B1 H N := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hc
  refine mem_B1_iff.2 ⟨f m, fun h => ?_⟩
  rw [cochainsMap1_apply, ← hm (φ h), map_sub, hequiv]

/-- A compatible pair sends continuous degree-two coboundaries to continuous degree-two
coboundaries. -/
theorem cochainsMap2_mem_B2 [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace M] [TopologicalSpace N] [IsTopologicalAddGroup M]
    [IsTopologicalAddGroup N] (φ : H →ₜ* G) (f : M →+ N)
    (hf : Continuous f) (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    {c : G × G → M} (hc : c ∈ B2 G M) :
    cochainsMap2 (φ : H →* G) f c ∈ B2 H N := by
  obtain ⟨b, hb, rfl⟩ := mem_B2_iff.1 hc
  refine mem_B2_iff.2 ⟨cochainsMap1 (φ : H →* G) f b,
    continuous_cochainsMap1 φ f hf hb, ?_⟩
  exact (cochainsMap2_d1 (φ : H →* G) f hequiv b).symm

end Naturality

section Cocycles

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M]
  (H : Type uH) [Monoid H] [TopologicalSpace H]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribSMul H N]

/-- A compatible pair sends continuous degree-one cocycles to continuous degree-one cocycles. -/
theorem cochainsMap1_mem_Z1 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) {c : G → M} (hc : c ∈ Z1 G M) :
    cochainsMap1 (φ : H →* G) f c ∈ Z1 H N := by
  refine mem_Z1_iff.2 ⟨continuous_cochainsMap1 φ f hf (mem_Z1_iff.1 hc).1,
    d1_apply_eq_zero_iff.1 ?_⟩
  rw [← cochainsMap2_d1 (φ : H →* G) f hequiv, d1_apply_eq_zero_iff.2 (mem_Z1_iff.1 hc).2,
    map_zero]

/-- A compatible pair sends continuous degree-two cocycles to continuous degree-two cocycles. -/
theorem cochainsMap2_mem_Z2 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    {c : G × G → M} (hc : c ∈ Z2 G M) :
    cochainsMap2 (φ : H →* G) f c ∈ Z2 H N := by
  refine mem_Z2_iff.2 ⟨continuous_cochainsMap2 φ f hf (mem_Z2_iff.1 hc).1, ?_⟩
  intro h k j
  simp only [cochainsMap2_apply, map_mul]
  rw [← hequiv h, ← map_add, ← map_add]
  exact congrArg f ((mem_Z2_iff.1 hc).2 ((φ : H →* G) h) ((φ : H →* G) k)
    ((φ : H →* G) j))

/-- The pullback of continuous degree-one cocycles along a compatible pair, sending a cocycle `c`
to `h ↦ f (c (φ h))`. -/
def cocyclesMap1 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) : Z1 G M →+ Z1 H N :=
  AddMonoidHom.codRestrict ((cochainsMap1 (φ : H →* G) f).domRestrict (Z1 G M))
    (Z1 H N) fun c => cochainsMap1_mem_Z1 G M H N φ f hf hequiv c.property

/-- The underlying cochain of `cocyclesMap1` is the degree-one cochain pullback. -/
@[simp]
theorem cocyclesMap1_coe (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z1 G M) :
    (cocyclesMap1 G M H N φ f hf hequiv c : H → N) = cochainsMap1 (φ : H →* G) f c := by
  ext h
  rfl

/-- The defining formula for the degree-one cocycle pullback, the pointwise form of
`cocyclesMap1_coe`. -/
theorem cocyclesMap1_apply (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z1 G M) (h : H) :
    (cocyclesMap1 G M H N φ f hf hequiv c : H → N) h =
      f ((c : G → M) (φ h)) :=
  by rfl

/-- Pullback of continuous cocycles along the identity compatible pair is the identity. -/
@[simp]
theorem cocyclesMap1_id (hid : ∀ (g : G) (m : M),
    (AddMonoidHom.id M) ((ContinuousMonoidHom.id G) g • m) = g • (AddMonoidHom.id M) m :=
      fun _ _ => rfl) :
    cocyclesMap1 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) continuous_id hid =
      AddMonoidHom.id _ := by
  ext c g
  simp only [cocyclesMap1_apply, ContinuousMonoidHom.coe_id, id_eq, AddMonoidHom.id_apply]

/-- Pullback of continuous cocycles along a composite compatible pair is the composite of the
pullbacks: it is contravariant in the group homomorphism and covariant in the coefficient map.
The compatibility of the composite pair follows from `ContinuousMonoidHom.comp_map_smul`. -/
theorem cocyclesMap1_comp
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n)
    (hcomp : ∀ (k : K) (m : M), (q.comp f) ((φ.comp ψ) k • m) = k • (q.comp f) m :=
      φ.comp_map_smul ψ f q hequiv hequivq) :
    cocyclesMap1 G M K P (φ.comp ψ) (q.comp f) (hq.comp hf) hcomp =
      (cocyclesMap1 H N K P ψ q hq hequivq).comp
        (cocyclesMap1 G M H N φ f hf hequiv) := by
  ext c k
  simp only [cocyclesMap1_apply, AddMonoidHom.comp_apply, ContinuousMonoidHom.coe_comp,
    Function.comp_apply]

/-- The pullback of continuous degree-two cocycles along a compatible pair. -/
def cocyclesMap2 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) : Z2 G M →+ Z2 H N :=
  AddMonoidHom.codRestrict ((cochainsMap2 (φ : H →* G) f).domRestrict (Z2 G M))
    (Z2 H N) fun c => cochainsMap2_mem_Z2 G M H N φ f hf hequiv c.property

/-- The underlying cochain of `cocyclesMap2` is the degree-two cochain pullback. -/
@[simp]
theorem cocyclesMap2_coe (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z2 G M) :
    (cocyclesMap2 G M H N φ f hf hequiv c : H × H → N) =
      cochainsMap2 (φ : H →* G) f c := by
  ext p
  rfl

/-- The defining formula for the degree-two cocycle pullback. -/
theorem cocyclesMap2_apply (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (c : Z2 G M) (h k : H) :
    (cocyclesMap2 G M H N φ f hf hequiv c : H × H → N) (h, k) =
      f ((c : G × G → M) (φ h, φ k)) :=
  by rfl

/-- Pullback of continuous degree-two cocycles along the identity compatible pair is the
identity. -/
@[simp]
theorem cocyclesMap2_id (hid : ∀ (g : G) (m : M),
    (AddMonoidHom.id M) ((ContinuousMonoidHom.id G) g • m) = g • (AddMonoidHom.id M) m :=
      fun _ _ => rfl) :
    cocyclesMap2 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) continuous_id hid =
      AddMonoidHom.id _ := by
  ext c p
  obtain ⟨g, h⟩ := p
  simp only [cocyclesMap2_apply, ContinuousMonoidHom.coe_id, id_eq, AddMonoidHom.id_apply]

/-- Pullback of continuous degree-two cocycles respects composition of compatible pairs. -/
theorem cocyclesMap2_comp
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n)
    (hcomp : ∀ (k : K) (m : M), (q.comp f) ((φ.comp ψ) k • m) = k • (q.comp f) m :=
      φ.comp_map_smul ψ f q hequiv hequivq) :
    cocyclesMap2 G M K P (φ.comp ψ) (q.comp f) (hq.comp hf) hcomp =
      (cocyclesMap2 H N K P ψ q hq hequivq).comp
        (cocyclesMap2 G M H N φ f hf hequiv) := by
  ext c p
  obtain ⟨k, l⟩ := p
  simp only [cocyclesMap2_apply, AddMonoidHom.comp_apply, ContinuousMonoidHom.coe_comp,
    Function.comp_apply]

end Cocycles

section Cohomology

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (H : Type uH) [Monoid H] [TopologicalSpace H]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction H N] [ContinuousSMul H N]

/-- Pullback on the explicit first continuous cohomology group along a compatible pair. -/
noncomputable def explicitMap1 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) : H1 G M →+ H1 H N :=
  QuotientAddGroup.map ((B1 G M).addSubgroupOf (Z1 G M))
    ((B1 H N).addSubgroupOf (Z1 H N)) (cocyclesMap1 G M H N φ f hf hequiv)
    fun _ hc => cochainsMap1_mem_B1 (φ : H →* G) f hequiv hc

/-- `explicitMap1` sends the class of a cocycle to the class of its pullback. -/
@[simp]
theorem explicitMap1_mk (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z1 G M) :
    explicitMap1 G M H N φ f hf hequiv (c : H1 G M) =
      (cocyclesMap1 G M H N φ f hf hequiv c : H1 H N) :=
  QuotientAddGroup.map_mk _ _ _ _ c

/-- Equality of compatible pairs gives equality of the induced maps on explicit `H¹`. -/
theorem explicitMap1_congr_of_eq
    (φ ψ : H →ₜ* G) (f q : M →+ N) {hf : Continuous f} {hq : Continuous q}
    {hφ : ∀ (h : H) (m : M), f (φ h • m) = h • f m}
    {hψ : ∀ (h : H) (m : M), q (ψ h • m) = h • q m}
    (hφeq : φ = ψ) (hfeq : f = q) :
    explicitMap1 G M H N φ f hf hφ = explicitMap1 G M H N ψ q hq hψ := by
  subst ψ q
  rfl

/-- Pullback by the identity compatible pair is the identity on explicit `H¹`. -/
@[simp]
theorem explicitMap1_id (hid : ∀ (g : G) (m : M),
    (AddMonoidHom.id M) ((ContinuousMonoidHom.id G) g • m) = g • (AddMonoidHom.id M) m :=
      fun _ _ => rfl) :
    explicitMap1 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) continuous_id hid =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap1_mk, AddMonoidHom.id_apply]
      exact congrArg (fun z : Z1 G M => (z : H1 G M))
        (DFunLike.congr_fun (cocyclesMap1_id G M hid) c)

/-- Pullback on explicit `H¹` respects composition of compatible pairs: it is contravariant in the
group homomorphism and covariant in the coefficient map. The compatibility of the composite pair
follows from `ContinuousMonoidHom.comp_map_smul`. -/
theorem explicitMap1_comp
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction K P] [ContinuousSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n)
    (hcomp : ∀ (k : K) (m : M), (q.comp f) ((φ.comp ψ) k • m) = k • (q.comp f) m :=
      φ.comp_map_smul ψ f q hequiv hequivq) :
    explicitMap1 G M K P (φ.comp ψ) (q.comp f) (hq.comp hf) hcomp =
      (explicitMap1 H N K P ψ q hq hequivq).comp
        (explicitMap1 G M H N φ f hf hequiv) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap1_mk, AddMonoidHom.comp_apply, explicitMap1_mk, explicitMap1_mk]
      exact congrArg (fun z : Z1 K P => (z : H1 K P))
        (DFunLike.congr_fun
          (cocyclesMap1_comp G M H N φ f hf hequiv K P ψ q hq hequivq hcomp) c)

/-- **Commuting squares of compatible pairs commute on explicit `H¹`**: if the composites
`φ ∘ ψ = φ' ∘ ψ'` of the group homomorphisms and `q ∘ f = q' ∘ f'` of the coefficient maps agree,
then pulling back along `(φ, f)` and then `(ψ, q)` agrees with pulling back along `(φ', f')` and
then `(ψ', q')`. This combines `explicitMap1_comp` and `explicitMap1_congr_of_eq` without asking
for the compatibility hypotheses of the composite pairs. -/
theorem explicitMap1_explicitMap1_of_comp_eq
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction K P] [ContinuousSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n)
    {H' : Type*} [Monoid H'] [TopologicalSpace H']
    {N' : Type*} [AddCommGroup N'] [TopologicalSpace N'] [IsTopologicalAddGroup N']
    [DistribMulAction H' N'] [ContinuousSMul H' N']
    (φ' : H' →ₜ* G) (f' : M →+ N') (hf' : Continuous f')
    (hequiv' : ∀ (h : H') (m : M), f' (φ' h • m) = h • f' m)
    (ψ' : K →ₜ* H') (q' : N' →+ P) (hq' : Continuous q')
    (hequivq' : ∀ (k : K) (n : N'), q' (ψ' k • n) = k • q' n)
    (hφ : φ.comp ψ = φ'.comp ψ') (hqf : q.comp f = q'.comp f') (x : H1 G M) :
    explicitMap1 H N K P ψ q hq hequivq (explicitMap1 G M H N φ f hf hequiv x) =
      explicitMap1 H' N' K P ψ' q' hq' hequivq' (explicitMap1 G M H' N' φ' f' hf' hequiv' x) := by
  rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
    ← explicitMap1_comp G M H N φ f hf hequiv K P ψ q hq hequivq,
    ← explicitMap1_comp G M H' N' φ' f' hf' hequiv' K P ψ' q' hq' hequivq']
  exact DFunLike.congr_fun (explicitMap1_congr_of_eq _ _ _ _ _ _ _ _ hφ hqf) x

/-- Pullback along a compatible pair made of a continuous multiplicative equivalence and an additive
equivalence of coefficients is an additive equivalence on explicit first continuous cohomology.
Both directions of the coefficient equivalence are required to be continuous; for discrete
coefficient modules this follows automatically from discreteness. -/
noncomputable def explicitMap1Equiv
    (φ : H ≃ₜ* G) (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m) : H1 G M ≃+ H1 H N := by
  have hequiv' : ∀ (g : G) (n : N), e.symm (φ.symm g • n) = g • e.symm n :=
    AddEquiv.symm_map_smul_of_map_mulEquiv_smul e φ.toMulEquiv hequiv
  exact
    { toFun := explicitMap1 G M H N φ e.toAddMonoidHom he hequiv
      invFun := explicitMap1 H N G M φ.symm e.symm.toAddMonoidHom he' hequiv'
      left_inv := fun x => DFunLike.congr_fun
        ((explicitMap1_comp G M H N φ e.toAddMonoidHom he hequiv
          G M φ.symm e.symm.toAddMonoidHom he' hequiv').symm.trans
          ((explicitMap1_congr_of_eq G M G M
            ((φ : H →ₜ* G).comp (φ.symm : G →ₜ* H)) (ContinuousMonoidHom.id G)
            (e.symm.toAddMonoidHom.comp e.toAddMonoidHom) (AddMonoidHom.id M)
            (hq := continuous_id) (hψ := fun _ _ => rfl)
            (ContinuousMonoidHom.ext φ.apply_symm_apply)
            (AddMonoidHom.ext e.symm_apply_apply)).trans (explicitMap1_id G M))) x
      right_inv := fun x => DFunLike.congr_fun
        ((explicitMap1_comp H N G M φ.symm e.symm.toAddMonoidHom he' hequiv'
          H N φ e.toAddMonoidHom he hequiv).symm.trans
          ((explicitMap1_congr_of_eq H N H N
            ((φ.symm : G →ₜ* H).comp (φ : H →ₜ* G)) (ContinuousMonoidHom.id H)
            (e.toAddMonoidHom.comp e.symm.toAddMonoidHom) (AddMonoidHom.id N)
            (hq := continuous_id) (hψ := fun _ _ => rfl)
            (ContinuousMonoidHom.ext φ.symm_apply_apply)
            (AddMonoidHom.ext e.apply_symm_apply)).trans (explicitMap1_id H N))) x
      map_add' := map_add (explicitMap1 G M H N φ e.toAddMonoidHom he hequiv) }

/-- The equivalence on explicit `H¹` is the pullback along its forward compatible pair. -/
@[simp]
theorem explicitMap1Equiv_apply
    (φ : H ≃ₜ* G) (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m) (x : H1 G M) :
    explicitMap1Equiv G M H N φ e he he' hequiv x =
      explicitMap1 G M H N φ e.toAddMonoidHom he hequiv x :=
  (rfl)

/-- The inverse of the equivalence on explicit `H¹` is the pullback along the inverse compatible
pair. -/
@[simp]
theorem explicitMap1Equiv_symm_apply
    (φ : H ≃ₜ* G) (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m) (x : H1 H N) :
    (explicitMap1Equiv G M H N φ e he he' hequiv).symm x =
      explicitMap1 H N G M φ.symm e.symm.toAddMonoidHom he'
        (AddEquiv.symm_map_smul_of_map_mulEquiv_smul e φ.toMulEquiv hequiv) x :=
  (rfl)

/-- Pullback on the explicit second continuous cohomology group along a compatible pair. -/
noncomputable def explicitMap2 [ContinuousMul G] [ContinuousMul H]
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) : H2 G M →+ H2 H N :=
  QuotientAddGroup.map ((B2 G M).addSubgroupOf (Z2 G M))
    ((B2 H N).addSubgroupOf (Z2 H N)) (cocyclesMap2 G M H N φ f hf hequiv)
    fun _ hc => cochainsMap2_mem_B2 (φ := φ) f hf hequiv hc

/-- `explicitMap2` sends the class of a cocycle to the class of its pullback. -/
@[simp]
theorem explicitMap2_mk [ContinuousMul G] [ContinuousMul H]
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z2 G M) :
    explicitMap2 G M H N φ f hf hequiv (c : H2 G M) =
      (cocyclesMap2 G M H N φ f hf hequiv c : H2 H N) :=
  QuotientAddGroup.map_mk _ _ _ _ c

/-- Equality of compatible pairs gives equality of the induced maps on explicit `H²`. -/
theorem explicitMap2_congr_of_eq [ContinuousMul G] [ContinuousMul H]
    (φ ψ : H →ₜ* G) (f q : M →+ N) {hf : Continuous f} {hq : Continuous q}
    {hφ : ∀ (h : H) (m : M), f (φ h • m) = h • f m}
    {hψ : ∀ (h : H) (m : M), q (ψ h • m) = h • q m}
    (hφeq : φ = ψ) (hfeq : f = q) :
    explicitMap2 G M H N φ f hf hφ = explicitMap2 G M H N ψ q hq hψ := by
  subst ψ q
  rfl

/-- Pullback by the identity compatible pair is the identity on explicit `H²`. -/
@[simp]
theorem explicitMap2_id [ContinuousMul G] (hid : ∀ (g : G) (m : M),
    (AddMonoidHom.id M) ((ContinuousMonoidHom.id G) g • m) = g • (AddMonoidHom.id M) m :=
      fun _ _ => rfl) :
    explicitMap2 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) continuous_id hid =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap2_mk, AddMonoidHom.id_apply]
      exact congrArg (fun z : Z2 G M => (z : H2 G M))
        (DFunLike.congr_fun (cocyclesMap2_id G M hid) c)

/-- Pullback on explicit `H²` respects composition of compatible pairs. -/
theorem explicitMap2_comp
    [ContinuousMul G] [ContinuousMul H]
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K] [ContinuousMul K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction K P] [ContinuousSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n)
    (hcomp : ∀ (k : K) (m : M), (q.comp f) ((φ.comp ψ) k • m) = k • (q.comp f) m :=
      φ.comp_map_smul ψ f q hequiv hequivq) :
    explicitMap2 G M K P (φ.comp ψ) (q.comp f) (hq.comp hf) hcomp =
      (explicitMap2 H N K P ψ q hq hequivq).comp
        (explicitMap2 G M H N φ f hf hequiv) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap2_mk, AddMonoidHom.comp_apply, explicitMap2_mk, explicitMap2_mk]
      exact congrArg (fun z : Z2 K P => (z : H2 K P))
        (DFunLike.congr_fun
          (cocyclesMap2_comp G M H N φ f hf hequiv K P ψ q hq hequivq hcomp) c)

/-- Pullback along a compatible pair made of a continuous multiplicative equivalence and an additive
equivalence of coefficients is an additive equivalence on explicit second continuous cohomology.
Both directions of the coefficient equivalence are required to be continuous; for discrete
coefficient modules this follows automatically from discreteness. -/
noncomputable def explicitMap2Equiv [ContinuousMul G] [ContinuousMul H]
    (φ : H ≃ₜ* G) (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m) : H2 G M ≃+ H2 H N := by
  have hequiv' : ∀ (g : G) (n : N), e.symm (φ.symm g • n) = g • e.symm n :=
    AddEquiv.symm_map_smul_of_map_mulEquiv_smul e φ.toMulEquiv hequiv
  exact
    { toFun := explicitMap2 G M H N φ e.toAddMonoidHom he hequiv
      invFun := explicitMap2 H N G M φ.symm e.symm.toAddMonoidHom he' hequiv'
      left_inv := fun x => DFunLike.congr_fun
        ((explicitMap2_comp G M H N φ e.toAddMonoidHom he hequiv
          G M φ.symm e.symm.toAddMonoidHom he' hequiv').symm.trans
          ((explicitMap2_congr_of_eq G M G M
            ((φ : H →ₜ* G).comp (φ.symm : G →ₜ* H)) (ContinuousMonoidHom.id G)
            (e.symm.toAddMonoidHom.comp e.toAddMonoidHom) (AddMonoidHom.id M)
            (hq := continuous_id) (hψ := fun _ _ => rfl)
            (ContinuousMonoidHom.ext φ.apply_symm_apply)
            (AddMonoidHom.ext e.symm_apply_apply)).trans (explicitMap2_id G M))) x
      right_inv := fun x => DFunLike.congr_fun
        ((explicitMap2_comp H N G M φ.symm e.symm.toAddMonoidHom he' hequiv'
          H N φ e.toAddMonoidHom he hequiv).symm.trans
          ((explicitMap2_congr_of_eq H N H N
            ((φ.symm : G →ₜ* H).comp (φ : H →ₜ* G)) (ContinuousMonoidHom.id H)
            (e.toAddMonoidHom.comp e.symm.toAddMonoidHom) (AddMonoidHom.id N)
            (hq := continuous_id) (hψ := fun _ _ => rfl)
            (ContinuousMonoidHom.ext φ.symm_apply_apply)
            (AddMonoidHom.ext e.apply_symm_apply)).trans (explicitMap2_id H N))) x
      map_add' := map_add (explicitMap2 G M H N φ e.toAddMonoidHom he hequiv) }

/-- The equivalence on explicit `H²` is the pullback along its forward compatible pair. -/
@[simp]
theorem explicitMap2Equiv_apply [ContinuousMul G] [ContinuousMul H]
    (φ : H ≃ₜ* G) (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m) (x : H2 G M) :
    explicitMap2Equiv G M H N φ e he he' hequiv x =
      explicitMap2 G M H N φ e.toAddMonoidHom he hequiv x :=
  (rfl)

/-- The inverse of the equivalence on explicit `H²` is the pullback along the inverse compatible
pair. -/
@[simp]
theorem explicitMap2Equiv_symm_apply [ContinuousMul G] [ContinuousMul H]
    (φ : H ≃ₜ* G) (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m) (x : H2 H N) :
    (explicitMap2Equiv G M H N φ e he he' hequiv).symm x =
      explicitMap2 H N G M φ.symm e.symm.toAddMonoidHom he'
        (AddEquiv.symm_map_smul_of_map_mulEquiv_smul e φ.toMulEquiv hequiv) x :=
  (rfl)

end Cohomology

section NamedMaps

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Restriction on explicit `H¹`, induced by the subgroup inclusion and the identity coefficient
map. -/
noncomputable def explicitRes1 (S : Subgroup G) : H1 G M →+ H1 S M :=
  explicitMap1 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
    continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M S)

/-- Restriction sends the class of a continuous `1`-cocycle to the class of its restriction. -/
@[simp]
theorem explicitRes1_mk (S : Subgroup G) (c : Z1 G M) :
    explicitRes1 G M S (c : H1 G M) =
      (cocyclesMap1 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
        continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M S) c : H1 S M) :=
  explicitMap1_mk G M S M _ _ _ _ c

/-- Restriction on explicit `H¹` is the compatible-pair pullback along the inclusion of the
subgroup with the identity on the coefficients, the degree-one counterpart of
`TauCeti.ContCohomology.explicitRes0_eq_explicitMap0`. -/
theorem explicitRes1_eq_explicitMap1 (S : Subgroup G) :
    explicitRes1 G M S =
      explicitMap1 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
        continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M S) := by
  rfl

/-- Restricting explicit `H¹` first to `S` and then to a subgroup `T` of `S` is restriction
along the composite inclusion. -/
theorem explicitRes1_comp (S : Subgroup G) (T : Subgroup S) :
    (explicitRes1 S M T).comp (explicitRes1 G M S) =
      explicitMap1 G M T M
        ((ContinuousMonoidHom.subgroupSubtype S).comp
          (ContinuousMonoidHom.subgroupSubtype T))
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) := by
  exact (explicitMap1_comp G M S M (ContinuousMonoidHom.subgroupSubtype S)
    (AddMonoidHom.id M) continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M S) T M
    (ContinuousMonoidHom.subgroupSubtype T) (AddMonoidHom.id M) continuous_id
    (ContinuousMonoidHom.id_subgroupSubtype_smul M T) (fun _ _ => rfl)).symm

/-- Restriction on explicit `H²`, induced by the subgroup inclusion and the identity coefficient
map. -/
noncomputable def explicitRes2 (S : Subgroup G) [ContinuousMul G] [ContinuousMul S] :
    H2 G M →+ H2 S M :=
  explicitMap2 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
    continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M S)

/-- Restriction sends the class of a continuous `2`-cocycle to the class of its restriction. -/
@[simp]
theorem explicitRes2_mk (S : Subgroup G) [ContinuousMul G] [ContinuousMul S] (c : Z2 G M) :
    explicitRes2 G M S (c : H2 G M) =
      (cocyclesMap2 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
        continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M S) c : H2 S M) :=
  explicitMap2_mk G M S M _ _ _ _ c

/-- Restriction on explicit `H²` is the compatible-pair pullback along the inclusion of the
subgroup with the identity on the coefficients. -/
theorem explicitRes2_eq_explicitMap2 (S : Subgroup G) [ContinuousMul G] [ContinuousMul S] :
    explicitRes2 G M S =
      explicitMap2 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
        continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M S) := by
  rfl

/-- Restricting explicit `H²` first to `S` and then to a subgroup `T` of `S` is restriction
along the composite inclusion. -/
theorem explicitRes2_comp (S : Subgroup G) (T : Subgroup S)
    [ContinuousMul G] [ContinuousMul S] [ContinuousMul T] :
    (explicitRes2 S M T).comp (explicitRes2 G M S) =
      explicitMap2 G M T M
        ((ContinuousMonoidHom.subgroupSubtype S).comp
          (ContinuousMonoidHom.subgroupSubtype T))
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) := by
  exact (explicitMap2_comp G M S M (ContinuousMonoidHom.subgroupSubtype S)
    (AddMonoidHom.id M) continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M S) T M
    (ContinuousMonoidHom.subgroupSubtype T) (AddMonoidHom.id M) continuous_id
    (ContinuousMonoidHom.id_subgroupSubtype_smul M T)).symm

end NamedMaps

section CoefficientMaps

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The coefficient map on explicit `H¹` induced by a continuous equivariant additive
homomorphism. -/
noncomputable def explicitCoeff1 {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) : H1 G M →+ H1 G N :=
  explicitMap1 G M G N (ContinuousMonoidHom.id G) f hf fun g m => f.map_smul g m

/-- A coefficient map sends a `1`-cocycle class to the class obtained by postcomposition. -/
@[simp]
theorem explicitCoeff1_mk {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) (c : Z1 G M) :
    explicitCoeff1 G M f hf (c : H1 G M) =
      (cocyclesMap1 G M G N (ContinuousMonoidHom.id G) f hf
        (fun g m => f.map_smul g m) c : H1 G N) :=
  explicitMap1_mk G M G N _ _ _ _ c

/-- A coefficient map on explicit `H¹` is the compatible-pair pullback along the identity of the
group, the degree-one counterpart of
`TauCeti.ContCohomology.explicitCoeff0_eq_explicitMap0`. -/
theorem explicitCoeff1_eq_explicitMap1 {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) :
    explicitCoeff1 G M f hf =
      explicitMap1 G M G N (ContinuousMonoidHom.id G) f hf (fun g m => f.map_smul g m) := by
  rfl

/-- The identity coefficient map induces the identity on explicit `H¹`. -/
@[simp]
theorem explicitCoeff1_id :
    explicitCoeff1 G M (DistribMulActionHom.id G) continuous_id = AddMonoidHom.id _ :=
  explicitMap1_id G M fun _ _ => rfl

/-- Coefficient maps on explicit `H¹` respect composition. -/
theorem explicitCoeff1_comp {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
    (f : M →+[G] N) (q : N →+[G] P) (hf : Continuous f) (hq : Continuous q) :
    explicitCoeff1 G M (q.comp f) (hq.comp hf) =
      (explicitCoeff1 G N q hq).comp (explicitCoeff1 G M f hf) := by
  -- The generic law writes the two identity group maps as their composite and the coefficient
  -- maps as unbundled additive homomorphisms; extensionality identifies those wrappers.
  convert explicitMap1_comp G M G N (ContinuousMonoidHom.id G) f hf
    (fun g m => f.map_smul g m) G P (ContinuousMonoidHom.id G) q hq
    (fun g n => q.map_smul g n) (fun g m => (q.comp f).map_smul g m) using 1 <;>
    ext <;> rfl

/-- An equivariant additive equivalence of topological coefficient modules induces an additive
equivalence on explicit first continuous cohomology. Both directions are required to be
continuous; for discrete coefficient modules this follows automatically from discreteness. -/
noncomputable def explicitCoeff1Equiv {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) : H1 G M ≃+ H1 G N :=
  explicitMap1Equiv G M G N (ContinuousMulEquiv.refl G) e he he' hequiv

/-- The coefficient equivalence on `H¹` is the coefficient map induced by its forward
equivariant additive homomorphism. -/
@[simp]
theorem explicitCoeff1Equiv_apply {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (x : H1 G M) :
    explicitCoeff1Equiv G M e he he' hequiv x =
      explicitCoeff1 G M { e.toAddMonoidHom with map_smul' := hequiv } he x :=
  (rfl)

/-- The inverse coefficient equivalence on `H¹` is the coefficient map induced by the inverse
equivariant additive homomorphism. -/
@[simp]
theorem explicitCoeff1Equiv_symm_apply {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (x : H1 G N) :
    (explicitCoeff1Equiv G M e he he' hequiv).symm x =
      explicitCoeff1 G N
        { e.symm.toAddMonoidHom with
          map_smul' := AddEquiv.symm_map_smul_of_map_smul e hequiv }
        he' x :=
  (rfl)

/-- On cocycle classes, the coefficient equivalence postcomposes the cocycle with the given
equivalence of coefficients. -/
theorem explicitCoeff1Equiv_mk {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (c : Z1 G M) :
    explicitCoeff1Equiv G M e he he' hequiv (c : H1 G M) =
      (cocyclesMap1 G M G N (ContinuousMonoidHom.id G)
        ({ e.toAddMonoidHom with map_smul' := hequiv } : M →+[G] N) he
        (fun g m => hequiv g m) c : H1 G N) := by
  let f : M →+[G] N := { e.toAddMonoidHom with map_smul' := hequiv }
  rw [explicitCoeff1Equiv_apply]
  exact explicitCoeff1_mk G M f he c

/-- The coefficient map on explicit `H²` induced by a continuous equivariant additive
homomorphism. -/
noncomputable def explicitCoeff2 [ContinuousMul G]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) : H2 G M →+ H2 G N :=
  explicitMap2 G M G N (ContinuousMonoidHom.id G) f hf fun g m => f.map_smul g m

/-- A coefficient map sends a `2`-cocycle class to the class obtained by postcomposition. -/
@[simp]
theorem explicitCoeff2_mk [ContinuousMul G]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) (c : Z2 G M) :
    explicitCoeff2 G M f hf (c : H2 G M) =
      (cocyclesMap2 G M G N (ContinuousMonoidHom.id G) f hf
        (fun g m => f.map_smul g m) c : H2 G N) :=
  explicitMap2_mk G M G N _ _ _ _ c

/-- A coefficient map on explicit `H²` is the compatible-pair pullback along the identity of the
group. -/
theorem explicitCoeff2_eq_explicitMap2 [ContinuousMul G]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) :
    explicitCoeff2 G M f hf =
      explicitMap2 G M G N (ContinuousMonoidHom.id G) f hf (fun g m => f.map_smul g m) := by
  rfl

/-- The identity coefficient map induces the identity on explicit `H²`. -/
@[simp]
theorem explicitCoeff2_id [ContinuousMul G] :
    explicitCoeff2 G M (DistribMulActionHom.id G) continuous_id = AddMonoidHom.id _ :=
  explicitMap2_id G M

/-- A coefficient map which is multiplication by `k` on `M` induces multiplication by `k` on
explicit `H²`: the class of a `2`-cocycle `c` goes to the class of `k • c`. -/
theorem explicitCoeff2_eq_nsmul [ContinuousMul G] (f : M →+[G] M) (hf : Continuous f) {k : ℕ}
    (hk : ∀ m, f m = k • m) (x : H2 G M) : explicitCoeff2 G M f hf x = k • x := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitCoeff2_mk, ← QuotientAddGroup.mk_nsmul]
    exact congrArg (fun z : Z2 G M ↦ (z : H2 G M))
      (Subtype.ext (funext fun ⟨g, h⟩ ↦ (cocyclesMap2_apply _ _ _ _ _ _ _ _ c g h).trans (hk _)))

/-- Coefficient maps on explicit `H²` respect composition. -/
theorem explicitCoeff2_comp [ContinuousMul G]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
    (f : M →+[G] N) (q : N →+[G] P) (hf : Continuous f) (hq : Continuous q) :
    explicitCoeff2 G M (q.comp f) (hq.comp hf) =
      (explicitCoeff2 G N q hq).comp (explicitCoeff2 G M f hf) := by
  -- As in degree one, extensionality identifies the generic compatible-pair composites with the
  -- identity group map and the bundled composite coefficient map.
  convert explicitMap2_comp G M G N (ContinuousMonoidHom.id G) f hf
    (fun g m => f.map_smul g m) G P (ContinuousMonoidHom.id G) q hq
    (fun g n => q.map_smul g n) using 1 <;>
    ext <;> rfl

/-- An equivariant additive equivalence of topological coefficient modules induces an additive
equivalence on explicit second continuous cohomology. Both directions are required to be
continuous; for discrete coefficient modules this follows automatically from discreteness. -/
noncomputable def explicitCoeff2Equiv [ContinuousMul G] {N : Type uN} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) : H2 G M ≃+ H2 G N :=
  explicitMap2Equiv G M G N (ContinuousMulEquiv.refl G) e he he' hequiv

/-- The coefficient equivalence on `H²` is the coefficient map induced by its forward
equivariant additive homomorphism. -/
@[simp]
theorem explicitCoeff2Equiv_apply [ContinuousMul G] {N : Type uN} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (x : H2 G M) :
    explicitCoeff2Equiv G M e he he' hequiv x =
      explicitCoeff2 G M { e.toAddMonoidHom with map_smul' := hequiv } he x :=
  (rfl)

/-- The inverse coefficient equivalence on `H²` is the coefficient map induced by the inverse
equivariant additive homomorphism. -/
@[simp]
theorem explicitCoeff2Equiv_symm_apply [ContinuousMul G] {N : Type uN} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (x : H2 G N) :
    (explicitCoeff2Equiv G M e he he' hequiv).symm x =
      explicitCoeff2 G N
        { e.symm.toAddMonoidHom with
          map_smul' := AddEquiv.symm_map_smul_of_map_smul e hequiv }
        he' x :=
  (rfl)

/-- A bijective equivariant homomorphism of discrete coefficient modules induces a bijection on
explicit first cohomology. -/
theorem explicitCoeff1_bijective [DiscreteTopology M] {N : Type uN} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [DiscreteTopology N] [DistribMulAction G N]
    [ContinuousSMul G N] {f : M →+[G] N} (hf : Function.Bijective f) :
    Function.Bijective (explicitCoeff1 G M f continuous_of_discreteTopology) := by
  have h := (explicitCoeff1Equiv G M (AddEquiv.ofBijective (f : M →+ N) hf)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (AddEquiv.ofBijective_smul hf)).bijective
  have e : ⇑(explicitCoeff1Equiv G M (AddEquiv.ofBijective (f : M →+ N) hf)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (AddEquiv.ofBijective_smul hf)) =
      ⇑(explicitCoeff1 G M f continuous_of_discreteTopology) := funext fun x => by
    rw [explicitCoeff1Equiv_apply]
    exact congrArg (fun φ : M →+[G] N => explicitCoeff1 G M φ continuous_of_discreteTopology x)
      (AddEquiv.ofBijective_toDistribMulActionHom hf)
  rwa [e] at h

/-- A bijective equivariant homomorphism of discrete coefficient modules induces a bijection on
explicit second cohomology. -/
theorem explicitCoeff2_bijective [ContinuousMul G] [DiscreteTopology M] {N : Type uN}
    [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] {f : M →+[G] N} (hf : Function.Bijective f) :
    Function.Bijective (explicitCoeff2 G M f continuous_of_discreteTopology) := by
  have h := (explicitCoeff2Equiv G M (AddEquiv.ofBijective (f : M →+ N) hf)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (AddEquiv.ofBijective_smul hf)).bijective
  have e : ⇑(explicitCoeff2Equiv G M (AddEquiv.ofBijective (f : M →+ N) hf)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (AddEquiv.ofBijective_smul hf)) =
      ⇑(explicitCoeff2 G M f continuous_of_discreteTopology) := funext fun x => by
    rw [explicitCoeff2Equiv_apply]
    exact congrArg (fun φ : M →+[G] N => explicitCoeff2 G M φ continuous_of_discreteTopology x)
      (AddEquiv.ofBijective_toDistribMulActionHom hf)
  rwa [e] at h

end CoefficientMaps

section Norm

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **The norm of a finite normal subgroup acts on explicit `H²` as multiplication by its order.**
The norm `m ↦ ∑ n : N, n • m` of a finite normal subgroup `N` of `G`, as a coefficient map,
induces multiplication by `#N` on `H²(G, M)`. The norm is `G`-equivariant because `N` is normal,
and it is multiplication by `#N` on the invariants, but not in general on `M`. -/
theorem explicitCoeff2_eq_card_nsmul (N : Subgroup G) [N.Normal] [Fintype N] (x : H2 G M) :
    explicitCoeff2 G M (groupNormHom N M) (continuous_groupNormHom N M) x = Nat.card N • x := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    obtain ⟨hcont, hc⟩ := mem_Z2_iff.1 c.2
    rw [explicitCoeff2_mk, ← QuotientAddGroup.mk_nsmul, H2pi_eq_iff, mem_B2_iff']
    -- The norm of `c` is `#N • c` plus the coboundary of `k ↦ ∑ n : N, (c (n, k) - c (k, n))`.
    refine ⟨fun k ↦ ∑ n : N, ((c : G × G → M) (n, k) - (c : G × G → M) (k, n)),
      continuous_finsetSum _ fun n _ ↦
        (hcont.comp (continuous_const.prodMk continuous_id)).sub
          (hcont.comp (continuous_id.prodMk continuous_const)), fun g h ↦ ?_⟩
    -- `cocyclesMap2_apply` is applied as a term: rewriting it would abstract the equivariance
    -- proof of the norm into an ill-typed motive.
    rw [Pi.sub_apply]
    refine Eq.trans ?_ (congrArg₂ (· - ·) (cocyclesMap2_apply _ _ _ _ _ _ _ _ c g h).symm rfl)
    simp only [ContinuousMonoidHom.coe_id, id, AddMonoidHom.coe_ofClass, groupNormHom_apply,
      groupNorm_apply, Subgroup.smul_def, AddSubgroup.coe_nsmul, Pi.smul_apply,
      TauCeti.groupCohomology.sum_smul_apply_of_isCocycle₂ N hc g h]
    abel

end Norm

end TauCeti.ContCohomology
