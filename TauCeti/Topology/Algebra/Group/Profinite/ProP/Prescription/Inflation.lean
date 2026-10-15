/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Equiv

/-!
# Inflation with twisted coefficients and the prescription property

Let `N` be a normal subgroup of a topological group `G`, let `π : G → G ⧸ N` be the quotient map
and let `χ : G ⧸ N →ₜ* ℤ_pˣ` be a continuous character. The subgroup `N` acts trivially on the
twisted module `I(χ ∘ π)/pⁱ`, so its `N`-invariants are all of it, and they are `I(χ)/pⁱ` as a
`G ⧸ N`-module. Reading the degree-one inflation `H¹(G ⧸ N, M ^ N) → H¹(G, M)` through this
identification gives the twisted inflation

```text
H¹(G ⧸ N, I(χ)/pⁱ) → H¹(G, I(χ ∘ π)/pⁱ),
```

which is injective and commutes with the reductions `I(χ)/pⁱ → I(χ)/pʲ`.

If moreover `N` has no nontrivial continuous `p`-group quotient, the twisted inflation is
bijective: by the inflation-restriction sequence its image is the kernel of restriction to `N`,
and `H¹(N, I(χ ∘ π)/pⁱ)` vanishes, because `N` acts trivially, so that its classes are the
continuous homomorphisms from `N` to the finite `p`-group `ℤ/pⁱ`, and there are none but `0`.
Consequently `χ` has the prescription property exactly when `χ ∘ π` has it. This applies to the
maximal pro-`p` quotient `G(p) = G ⧸ proPKernel p G` of a profinite group `G`, whose pro-`p`
kernel has no `p`-quotient (`TauCeti.proPKernel_proPKernel_eq_top`): a character of `G(p)` has the
prescription property if and only if its pullback to `G` does. For `G` an absolute Galois group,
this reduces the prescription property of a character of the maximal pro-`p` Galois group, such
as a descended cyclotomic character, to the corresponding statement about the absolute Galois
group itself, where Kummer theory is available.

## Main definitions

* `TauCeti.ZModTwist.fixedPointsEquiv`: the identification of the `N`-invariants of
  `I(χ ∘ π)/pⁱ` with `I(χ)/pⁱ`, equivariant for `G ⧸ N`.
* `TauCeti.explicitInfl1ZModTwist`: twisted inflation `H¹(G ⧸ N, I(χ)/pⁱ) → H¹(G, I(χ ∘ π)/pⁱ)`.

## Main results

* `TauCeti.explicitInfl1ZModTwist_eq_explicitMap1`: twisted inflation is the pullback along
  `G → G ⧸ N`, with the identity on residue classes as coefficient map.
* `TauCeti.explicitInfl1ZModTwist_injective`: twisted inflation is injective.
* `TauCeti.explicitCoeff1_reduce_comp_explicitInfl1ZModTwist`: twisted inflation commutes with
  the reductions between levels.
* `TauCeti.explicitInfl1ZModTwist_bijective`: twisted inflation is bijective when `N` has no
  nontrivial continuous `p`-group quotient.
* `TauCeti.hasPrescriptionProperty_comp_quotientMk_iff`: `χ ∘ π` has the prescription property
  exactly when `χ` does, under the same hypothesis on `N`.
* `TauCeti.hasPrescriptionProperty_comp_quotientMk_proPKernel_iff`: the case of the maximal
  pro-`p` quotient of a profinite group.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.7).
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  (N : Subgroup G) [N.Normal] (χ : G ⧸ N →ₜ* ℤ_[p]ˣ) (i : ℕ)

namespace ZModTwist

/-- The normal subgroup `N` acts trivially on the twisted module of a character pulled back from
`G ⧸ N`, because the pulled-back character is `1` on `N`. -/
theorem smul_eq_self_of_mem {n : G} (hn : n ∈ N)
    (x : ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i) : n • x = x := by
  have h1 : ContinuousMonoidHom.quotientMk N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
  ext
  simp [val_smul, h1]

/-- The `N`-invariants of `I(χ ∘ π)/pⁱ`, which are all of it (`smul_eq_self_of_mem`), are
`I(χ)/pⁱ`. On residue classes this is the identity; it is `G ⧸ N`-equivariant
(`fixedPointsEquiv_smul`). -/
def fixedPointsEquiv :
    FixedPoints.addSubgroup N (ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i) ≃+
      ZModTwist χ i where
  toFun x := ⟨(x : ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i).val⟩
  invFun y := ⟨⟨y.val⟩, (FixedPoints.mem_addSubgroup _ _ _).2 fun n =>
    smul_eq_self_of_mem N χ i n.2 _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The identification of the invariants is the identity on residue classes. -/
@[simp]
theorem val_fixedPointsEquiv
    (x : FixedPoints.addSubgroup N (ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i)) :
    (fixedPointsEquiv N χ i x).val =
      (x : ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i).val :=
  (rfl)

/-- The inverse identification of the invariants is the identity on residue classes. -/
@[simp]
theorem val_coe_fixedPointsEquiv_symm (y : ZModTwist χ i) :
    (((fixedPointsEquiv N χ i).symm y :
      ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i)).val = y.val :=
  (rfl)

/-- The identification of the invariants is equivariant for the quotient action of `G ⧸ N`. -/
theorem fixedPointsEquiv_smul (q : G ⧸ N)
    (x : FixedPoints.addSubgroup N (ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i)) :
    fixedPointsEquiv N χ i (q • x) = q • fixedPointsEquiv N χ i x := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [coe_quotient_smul_fixedPoints_addSubgroup]
    ext
    simp [coe_smul_fixedPoints_addSubgroup, val_smul]

end ZModTwist

/-- **Twisted inflation** `H¹(G ⧸ N, I(χ)/pⁱ) → H¹(G, I(χ ∘ π)/pⁱ)`: degree-one inflation
`TauCeti.ContCohomology.explicitInfl1`, read through the identification
`TauCeti.ZModTwist.fixedPointsEquiv` of the `N`-invariants of `I(χ ∘ π)/pⁱ` with `I(χ)/pⁱ`. -/
noncomputable def explicitInfl1ZModTwist :
    H1 (G ⧸ N) (ZModTwist χ i) →+
      H1 G (ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i) :=
  (explicitInfl1 G (ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i) N).comp
    (explicitCoeff1Equiv (G ⧸ N) (ZModTwist χ i) (ZModTwist.fixedPointsEquiv N χ i).symm
      continuous_of_discreteTopology continuous_of_discreteTopology
      (fun q y => AddEquiv.symm_map_smul_of_map_smul _
        (ZModTwist.fixedPointsEquiv_smul N χ i) q y)).toAddMonoidHom

/-- Twisted inflation is the pullback along the quotient map `G → G ⧸ N`, paired with the
identification `TauCeti.ZModTwist.compEquiv` of `I(χ)/pⁱ` with `I(χ ∘ π)/pⁱ`, which is the identity
on residue classes. -/
theorem explicitInfl1ZModTwist_eq_explicitMap1 :
    explicitInfl1ZModTwist N χ i =
      explicitMap1 (G ⧸ N) (ZModTwist χ i) G
        (ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i)
        (ContinuousMonoidHom.quotientMk N)
        (ZModTwist.compEquiv (ContinuousMonoidHom.quotientMk N) χ i).toAddMonoidHom
        continuous_of_discreteTopology
        (fun g x => ZModTwist.compEquiv_smul (ContinuousMonoidHom.quotientMk N) χ i g x) := by
  ext c
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, explicitInfl1ZModTwist,
    AddEquiv.coe_toAddMonoidHom, explicitCoeff1Equiv_mk, explicitInfl1_mk]
  refine Eq.trans ?_ (explicitMap1_mk _ _ _ _ _ _ _ _ c).symm
  congr 1
  refine Subtype.ext (funext fun g => ZModTwist.ext ?_)
  -- `erw`: the continuity arguments of `cocyclesMap1_apply` are stated for the coerced additive
  -- homomorphisms, which `rw` and `simp` cannot match against the bundled ones here.
  erw [cocyclesMap1_apply, cocyclesMap1_apply, cocyclesMap1_apply]
  exact (ZModTwist.compEquiv_apply _ χ i ((c : G ⧸ N → ZModTwist χ i) g)).symm

/-- Twisted inflation is injective. -/
theorem explicitInfl1ZModTwist_injective : Function.Injective (explicitInfl1ZModTwist N χ i) :=
  (explicitInfl1_injective _ _ _).comp (AddEquiv.injective _)

/-- **Twisted inflation commutes with the reductions** `I(χ)/pⁱ → I(χ)/pʲ`: on cocycles both
composites send a cocycle on `G ⧸ N` to the same cocycle on `G`. -/
theorem explicitCoeff1_reduce_comp_explicitInfl1ZModTwist {j : ℕ} (hij : j ≤ i) :
    (explicitCoeff1 G (ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i)
        (ZModTwist.reduce (χ.comp (ContinuousMonoidHom.quotientMk N)) hij)
        continuous_of_discreteTopology).comp (explicitInfl1ZModTwist N χ i) =
      (explicitInfl1ZModTwist N χ j).comp
        (explicitCoeff1 (G ⧸ N) (ZModTwist χ i) (ZModTwist.reduce χ hij)
          continuous_of_discreteTopology) := by
  ext c
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, explicitInfl1ZModTwist,
    AddEquiv.coe_toAddMonoidHom, explicitCoeff1Equiv_mk, explicitInfl1_mk, explicitCoeff1_mk]
  congr 1
  refine Subtype.ext (funext fun g => ZModTwist.ext ?_)
  -- `erw`: the continuity arguments of `cocyclesMap1_apply` are stated for the coerced additive
  -- homomorphisms, which `rw` and `simp` cannot match against the bundled equivariant ones here.
  erw [cocyclesMap1_apply, cocyclesMap1_apply, cocyclesMap1_apply, cocyclesMap1_apply,
    cocyclesMap1_apply, cocyclesMap1_apply]
  exact (ZModTwist.val_reduce (χ.comp (ContinuousMonoidHom.quotientMk N)) hij
    ⟨((c : G ⧸ N → ZModTwist χ i) g).val⟩).trans
      (ZModTwist.val_reduce χ hij ((c : G ⧸ N → ZModTwist χ i) g)).symm

/-- **Twisted inflation is bijective** when `N` has no nontrivial continuous `p`-group quotient.
Its image is the kernel of restriction to `N` (`TauCeti.ContCohomology.explicitInfRes_exact`), and
`H¹(N, I(χ ∘ π)/pⁱ)` vanishes: `N` acts trivially, so its classes are continuous homomorphisms
from `N` to the finite `p`-group `ℤ/pⁱ` (`TauCeti.ContCohomology.H1EquivOfSmulEqSelf`), and these
are trivial (`TauCeti.eq_one_of_proPKernel_eq_top`). -/
theorem explicitInfl1ZModTwist_bijective (hN : proPKernel p N = ⊤) :
    Function.Bijective (explicitInfl1ZModTwist N χ i) := by
  refine ⟨explicitInfl1ZModTwist_injective N χ i, fun x => ?_⟩
  set M := ZModTwist (χ.comp (ContinuousMonoidHom.quotientMk N)) i
  have htriv : ∀ (n : N) (m : M), n • m = m := fun n m => ZModTwist.smul_eq_self_of_mem N χ i n.2 m
  have hsub : Subsingleton (H1 N M) := by
    refine (H1EquivOfSmulEqSelf htriv).toEquiv.subsingleton_congr.2 ⟨fun φ ψ => ?_⟩
    have h (φ : Additive (ContinuousMonoidHom N (Multiplicative M))) : φ = 0 :=
      Additive.toMul.injective <| ContinuousMonoidHom.toMonoidHom_injective <|
        eq_one_of_proPKernel_eq_top hN (ZModTwist.isProP_multiplicative _ i) _
          (Additive.toMul φ).continuous
    rw [h φ, h ψ]
  have hx : x ∈ (explicitRes1 G M N).ker := AddMonoidHom.mem_ker.2 (Subsingleton.elim _ _)
  rw [← explicitInfRes_exact] at hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, rfl⟩ := (explicitCoeff1Equiv (G ⧸ N) (ZModTwist χ i)
    (ZModTwist.fixedPointsEquiv N χ i).symm continuous_of_discreteTopology
    continuous_of_discreteTopology (fun q y => AddEquiv.symm_map_smul_of_map_smul _
      (ZModTwist.fixedPointsEquiv_smul N χ i) q y)).surjective y
  exact ⟨z, rfl⟩

/-- **The prescription property descends along a quotient with no `p`-quotient kernel.** If `N`
has no nontrivial continuous `p`-group quotient, a character `χ` of `G ⧸ N` has the prescription
property exactly when its pullback `χ ∘ π` to `G` does: twisted inflation identifies the
reductions `H¹(-, I(-)/pⁱ) → H¹(-, I(-)/p)` of the two groups. -/
theorem hasPrescriptionProperty_comp_quotientMk_iff (hN : proPKernel p N = ⊤) :
    HasPrescriptionProperty (χ.comp (ContinuousMonoidHom.quotientMk N)) ↔
      HasPrescriptionProperty χ := by
  simp only [hasPrescriptionProperty_iff]
  refine forall₂_congr fun k hk => ⟨fun h y => ?_, fun h y => ?_⟩
  · obtain ⟨z, hz⟩ := h (explicitInfl1ZModTwist N χ 1 y)
    obtain ⟨w, rfl⟩ := (explicitInfl1ZModTwist_bijective N χ k hN).2 z
    refine ⟨w, explicitInfl1ZModTwist_injective N χ 1 ?_⟩
    rw [← hz]
    exact (DFunLike.congr_fun (explicitCoeff1_reduce_comp_explicitInfl1ZModTwist N χ k hk) w).symm
  · obtain ⟨x, rfl⟩ := (explicitInfl1ZModTwist_bijective N χ 1 hN).2 y
    obtain ⟨w, rfl⟩ := h x
    exact ⟨explicitInfl1ZModTwist N χ k w,
      DFunLike.congr_fun (explicitCoeff1_reduce_comp_explicitInfl1ZModTwist N χ k hk) w⟩

/-- **The prescription property on the maximal pro-`p` quotient.** For a profinite group `G`, a
character of its maximal pro-`p` quotient `G(p)` has the prescription property exactly when its
pullback to `G` does. -/
theorem hasPrescriptionProperty_comp_quotientMk_proPKernel_iff [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (χ : maximalProPQuotient p G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty (χ.comp (ContinuousMonoidHom.quotientMk (proPKernel p G))) ↔
      HasPrescriptionProperty χ :=
  hasPrescriptionProperty_comp_quotientMk_iff _ χ proPKernel_proPKernel_eq_top

end TauCeti
