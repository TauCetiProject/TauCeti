/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CompletedGroupAlgebraModule
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.NormalClosure
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# The abelianized kernel of a character as a module over the completed group algebra

Let `G` be a pro-`p` group and `N` a closed normal subgroup. The topological abelianization
`N^{ab} = N ⧸ (N, N)` is an abelian pro-`p` group on which `G ⧸ N` acts continuously by
conjugation, so it is a compact module over the completed group algebra `ℤ_p[[G ⧸ N]]`
(`TauCeti.IsProP.completedGroupAlgebraModule`). This file proves that this module is **finitely
generated** as soon as `N` is the closed normal closure of a finite set `S`: the conjugates of `S`
generate a dense subgroup of `N`, so the `(G ⧸ N)`-orbit of the classes of the elements of `S`
generates a dense subgroup of `N^{ab}`, and a finite set with a dense orbit spans a compact module
over a compact ring.

A closed normal subgroup `N` with commutative quotient, for `G` topologically finitely generated,
is such a subgroup (`IsProP.exists_finite_topologicalClosure_normalClosure_eq`, in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.NormalClosure`). The kernel of a continuous
character `χ : G → A` to a commutative group is the case of interest.

For `F` free pro-`p` of finite rank and `χ : F → ℤ_pˣ` an orientation character, the module
obtained is `E = X ⧸ (X, X)`, `X = ker χ`, over `Λ = ℤ_p[[Γ]]`, `Γ = F ⧸ X ≅ Im χ`, on which
Labute's classification of Demushkin groups runs (Labute, §4, p. 121): `E` is generated over `Λ`
by finitely many classes of elements of `X`, and it is this finite generation that lets the
relator class be expressed as a `Λ`-combination of generators.

**The convention for the action.** Labute writes the action of `Γ` on `E` as
`[y] · [x] = [y⁻¹ x y]` (§4 Definition, p. 121). The module structure used here is Mathlib's
conjugation action `[y] • [x] = [y x y⁻¹]` (`TopologicalAbelianization.mk_smul_mk`, extended to the
group elements of `Λ` by `TauCeti.IsProP.completedGroupAlgebraModule_of_smul`), so Labute's
action is `[y]⁻¹ • [x]` (`TopologicalAbelianization.mk_inv_smul_mk`): the two differ by the
inversion of `Γ`. Since `Γ ≅ Im χ` is commutative, inversion is a continuous automorphism of `Γ`,
and `TauCeti.completedGroupAlgebra.map` turns it into an involutive algebra automorphism `ι` of
`Λ` with Labute's scalar action `l ·_L ξ = ι l • ξ`. The two module structures therefore have the
same submodules, the same spans and the same generating sets, and the finite generation proved
here holds verbatim for Labute's action; only the coefficients of a `Λ`-combination of given
generators change, by `ι`. No such coefficients are computed in this file.

## Main results

* `IsProP.span_completedGroupAlgebraModule_topologicalAbelianization_eq_top`,
  `IsProP.module_finite_completedGroupAlgebraModule_topologicalAbelianization`: if `N` is
  the closed normal closure of a finite set `S` in a pro-`p` group `G`, then the classes of the
  elements of `S` span `N^{ab}` over `ℤ_p[[G ⧸ N]]`, so `N^{ab}` is a finitely generated module.
* `IsProP.exists_finite_span_completedGroupAlgebraModule_topologicalAbelianization_eq_top`,
  `IsProP.module_finite_completedGroupAlgebraModule_topologicalAbelianization_of_commutator_le`:
  for such an `N`, the classes of some finite subset of `N` span `N^{ab}` over `ℤ_p[[G ⧸ N]]`, so
  `N^{ab}` is a finitely generated module.
* `IsProP.exists_finite_span_completedGroupAlgebraModule_topologicalAbelianization_ker_eq_top`,
  `IsProP.module_finite_completedGroupAlgebraModule_topologicalAbelianization_ker`:
  Labute's module, the abelianized kernel of a continuous character of a topologically finitely
  generated pro-`p` group, is spanned over the completed group algebra of the image by the classes
  of some finite subset of the kernel, so it is a finitely generated module.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4.
-/

public section

namespace TauCeti.IsProP

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

section NormalClosure

variable (hG : IsProP p G) (N : Subgroup G) [N.Normal]
include hG

/-- **The classes of the normal generators of a closed subgroup span its abelianization over the
completed group algebra.** If `N` is the closed normal closure of a finite set `S` in a pro-`p`
group `G`, then the classes of the elements of `S` span `N^{ab}` over `ℤ_p[[G ⧸ N]]`, for the
module structure `TauCeti.IsProP.completedGroupAlgebraModule` through conjugation: their
`(G ⧸ N)`-orbit generates a dense subgroup, and a finite set with a dense orbit spans a compact
module over a compact ring. -/
theorem span_completedGroupAlgebraModule_topologicalAbelianization_eq_top {S : Set G}
    (hS : S.Finite) (hSN : (Subgroup.normalClosure S).topologicalClosure = N) :
    haveI : IsClosed (N : Set G) := hSN ▸ Subgroup.isClosed_topologicalClosure _
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Submodule.span (completedGroupAlgebra ℤ_[p] (G ⧸ N)) (Additive.ofMul ''
      ((QuotientGroup.mk : N → TopologicalAbelianization N) '' (Subtype.val ⁻¹' S))) = ⊤ := by
  have : IsClosed (N : Set G) := hSN ▸ Subgroup.isClosed_topologicalClosure _
  exact (hG.topologicalAbelianization N).span_completedGroupAlgebraModule_eq_top (G ⧸ N)
    ((hS.preimage Subtype.val_injective.injOn).image _)
    (Subgroup.dense_iff_topologicalClosure_eq_top.2
      (TopologicalAbelianization.topologicalClosure_closure_univ_smul_image_mk_eq_top hSN))

/-- **The abelianization of a finitely normally generated closed subgroup is a finitely generated
module over the completed group algebra.** If `N` is the closed normal closure of a finite set `S`
in a pro-`p` group `G`, then `N^{ab}` is a finitely generated `ℤ_p[[G ⧸ N]]`-module, for the
module structure `TauCeti.IsProP.completedGroupAlgebraModule` through conjugation, spanned by the
classes of the elements of `S`
(`IsProP.span_completedGroupAlgebraModule_topologicalAbelianization_eq_top`). -/
theorem module_finite_completedGroupAlgebraModule_topologicalAbelianization {S : Set G}
    (hS : S.Finite) (hSN : (Subgroup.normalClosure S).topologicalClosure = N) :
    haveI : IsClosed (N : Set G) := hSN ▸ Subgroup.isClosed_topologicalClosure _
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Module.Finite (completedGroupAlgebra ℤ_[p] (G ⧸ N))
      (Additive (TopologicalAbelianization N)) :=
  haveI : IsClosed (N : Set G) := hSN ▸ Subgroup.isClosed_topologicalClosure _
  letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  Module.finite_def.2
    (hG.span_completedGroupAlgebraModule_topologicalAbelianization_eq_top N hS hSN ▸
      Submodule.fg_span (((hS.preimage Subtype.val_injective.injOn).image _).image _))

end NormalClosure

section CommutatorLe

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
include hG hfg

/-- **A closed normal subgroup with commutative quotient has finitely generated abelianization
over the completed group algebra, with named generators.** For `N` a closed normal subgroup of a
topologically finitely generated pro-`p` group `G` containing the commutator subgroup, the classes
of the elements of some finite subset of `N` span `N^{ab}` over `ℤ_p[[G ⧸ N]]`, for the module
structure `TauCeti.IsProP.completedGroupAlgebraModule` through conjugation. -/
theorem exists_finite_span_completedGroupAlgebraModule_topologicalAbelianization_eq_top
    {N : Subgroup G} [N.Normal] [IsClosed (N : Set G)] (hc : commutator G ≤ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    ∃ S : Set G, S.Finite ∧ S ⊆ N ∧ Submodule.span (completedGroupAlgebra ℤ_[p] (G ⧸ N))
      (Additive.ofMul ''
        ((QuotientGroup.mk : N → TopologicalAbelianization N) '' (Subtype.val ⁻¹' S))) = ⊤ := by
  obtain ⟨S, hS, hSN⟩ := hG.exists_finite_topologicalClosure_normalClosure_eq hfg ‹_› hc
  exact ⟨S, hS, (Subgroup.topologicalClosure_normalClosure_le_iff ‹_›).1 hSN.le,
    hG.span_completedGroupAlgebraModule_topologicalAbelianization_eq_top N hS hSN⟩

/-- **A closed normal subgroup with commutative quotient has finitely generated abelianization
over the completed group algebra.** For `N` a closed normal subgroup of a topologically finitely
generated pro-`p` group `G` containing the commutator subgroup, `N^{ab}` is a finitely generated
`ℤ_p[[G ⧸ N]]`-module, for the module structure `TauCeti.IsProP.completedGroupAlgebraModule`
through conjugation; the generators are the classes of a finite subset of `N`
(`IsProP.exists_finite_span_completedGroupAlgebraModule_topologicalAbelianization_eq_top`).
-/
theorem module_finite_completedGroupAlgebraModule_topologicalAbelianization_of_commutator_le
    {N : Subgroup G} [N.Normal] [IsClosed (N : Set G)] (hc : commutator G ≤ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Module.Finite (completedGroupAlgebra ℤ_[p] (G ⧸ N))
      (Additive (TopologicalAbelianization N)) := by
  obtain ⟨S, hS, hSN⟩ := hG.exists_finite_topologicalClosure_normalClosure_eq hfg ‹_› hc
  exact hG.module_finite_completedGroupAlgebraModule_topologicalAbelianization N hS hSN

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A] (χ : G →* A)
  (hχ : Continuous χ)
include hχ

/-- **Labute's module is generated by the classes of finitely many elements of the kernel.** For a
continuous character `χ : G → A` of a topologically finitely generated pro-`p` group `G` to a
commutative `T1` group, the topological abelianization `E = X ⧸ (X, X)` of `X = ker χ` is spanned
over the completed group algebra `Λ = ℤ_p[[G ⧸ X]]` by the classes of the elements of some finite
subset of `X`, for the module structure `TauCeti.IsProP.completedGroupAlgebraModule` through
conjugation `[y] • [x] = [y x y⁻¹]`. The finite subset is the normal generating set of `X`
produced by `exists_finite_topologicalClosure_normalClosure_eq_ker`, not a set of prescribed basis
elements of `G`; the expression of the relator class in a normalized basis is a later step of the
classification. -/
theorem exists_finite_span_completedGroupAlgebraModule_topologicalAbelianization_ker_eq_top :
    haveI : IsClosed (χ.ker : Set G) := χ.coe_ker ▸ isClosed_singleton.preimage hχ
    letI := (hG.topologicalAbelianization χ.ker).completedGroupAlgebraModule (G ⧸ χ.ker)
    ∃ S : Set G, S.Finite ∧ S ⊆ χ.ker ∧ Submodule.span (completedGroupAlgebra ℤ_[p] (G ⧸ χ.ker))
      (Additive.ofMul '' ((QuotientGroup.mk : χ.ker → TopologicalAbelianization χ.ker) ''
        (Subtype.val ⁻¹' S))) = ⊤ :=
  haveI : IsClosed (χ.ker : Set G) := χ.coe_ker ▸ isClosed_singleton.preimage hχ
  hG.exists_finite_span_completedGroupAlgebraModule_topologicalAbelianization_eq_top hfg
    (Abelianization.commutator_subset_ker χ)

/-- **Labute's module is finitely generated.** For a continuous character `χ : G → A` of a
topologically finitely generated pro-`p` group `G` to a commutative `T1` group, the topological
abelianization `E = X ⧸ (X, X)` of `X = ker χ` is a finitely generated module over the completed
group algebra `Λ = ℤ_p[[G ⧸ X]]`, for the module structure
`TauCeti.IsProP.completedGroupAlgebraModule` through conjugation `[y] • [x] = [y x y⁻¹]`. For `G`
free pro-`p` of finite rank and `χ` an orientation `G → ℤ_pˣ` this is the module of Labute, §4,
on which the classification of Demushkin groups runs, with his action `[y] · [x] = [y⁻¹ x y]`
composed with the inversion of `Γ`; finite generation is the same statement for both conventions
(see the module docstring). The generators are the classes of a finite subset of `X`
(`IsProP.exists_finite_span_completedGroupAlgebraModule_topologicalAbelianization_ker_eq_top`).
-/
theorem module_finite_completedGroupAlgebraModule_topologicalAbelianization_ker :
    haveI : IsClosed (χ.ker : Set G) := χ.coe_ker ▸ isClosed_singleton.preimage hχ
    letI := (hG.topologicalAbelianization χ.ker).completedGroupAlgebraModule (G ⧸ χ.ker)
    Module.Finite (completedGroupAlgebra ℤ_[p] (G ⧸ χ.ker))
      (Additive (TopologicalAbelianization χ.ker)) :=
  haveI : IsClosed (χ.ker : Set G) := χ.coe_ker ▸ isClosed_singleton.preimage hχ
  hG.module_finite_completedGroupAlgebraModule_topologicalAbelianization_of_commutator_le hfg
    (Abelianization.commutator_subset_ker χ)

end CommutatorLe

end TauCeti.IsProP
