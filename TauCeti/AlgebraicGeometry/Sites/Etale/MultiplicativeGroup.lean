/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf
public import TauCeti.AlgebraicGeometry.Sites.Fpqc

/-!
# The sheaves `𝔾_m` and `μ_n` on the small étale site

Let `S` be a scheme. A sheaf on the big fpqc site `Over S` restricts to the small étale site
`S.Etale` of schemes étale over `S`, along the forgetful functor `S.Etale ⥤ Over S`: its value on
an étale `U ⟶ S` is its value on `U` as an `S`-scheme
(`AlgebraicGeometry.Scheme.restrictSmallEtale`, in `TauCeti.AlgebraicGeometry.Sites.Fpqc`). The
restriction is a sheaf for the small étale topology, since a sheaf for the fpqc topology is one
for the coarser étale topology and the forgetful functor is continuous for the étale topology
(`AlgebraicGeometry.Scheme.isContinuous_etaleForget_fpqcTopology`).

Restricting the sheaves `𝔾_m : T ↦ Γ(T, 𝒪_T)ˣ` and `μ_n : T ↦ {t ∈ Γ(T, 𝒪_T)ˣ | tⁿ = 1}` of the
big site gives `GmEtale S` and `muEtale S n` (Stacks, Section 59.28 (03PK)), with the inclusion
`μ_n ⟶ 𝔾_m` and the `n`-th power map of `𝔾_m`. Their values on an étale `U ⟶ S` are the units of
`Γ(U, 𝒪_U)` and their `n`-th roots of unity (`GmEtale_obj`, `muEtale_obj`): the restriction of
`𝔾_m` to the small étale site is `U ↦ Γ(U, 𝒪_U)ˣ`. Restriction preserves limits, so `μ_n` is still
the kernel of the `n`-th power map of `𝔾_m` on the small étale site
(`isLimitMuEtaleKernelFork`), for every `n`; it is a sheaf on the small étale site even when `n`
is not invertible on `S`.

## Main declarations

* `AlgebraicGeometry.Scheme.GmEtale S`, `AlgebraicGeometry.Scheme.muEtale S n`: the sheaves `𝔾_m`
  and `μ_n` on the small étale site of `S`, written additively.
* `AlgebraicGeometry.Scheme.muToGmEtale`, `AlgebraicGeometry.Scheme.powHomEtale`: the inclusion
  `μ_n ⟶ 𝔾_m` and the `n`-th power map `𝔾_m ⟶ 𝔾_m` on the small étale site.
* `AlgebraicGeometry.Scheme.isLimitMuEtaleKernelFork`: `μ_n` is the kernel of the `n`-th power
  map on the small étale site.

## References

* [Stacks Project, Section 59.28 (03PK)](https://stacks.math.columbia.edu/tag/03PK)
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The multiplicative group `𝔾_m : U ↦ Γ(U, 𝒪_U)ˣ` on the small étale site of `S`, written
additively: the restriction of the big-site `𝔾_m`. -/
noncomputable abbrev GmEtale : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u} :=
  (restrictSmallEtale S).obj (Gm S)

/-- The sheaf `μ_n : U ↦ {t ∈ Γ(U, 𝒪_U)ˣ | tⁿ = 1}` of `n`-th roots of unity on the small étale
site of `S`, written additively: the restriction of the big-site `μ_n`. -/
noncomputable abbrev muEtale (n : ℕ) : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u} :=
  (restrictSmallEtale S).obj (mu S n)

/-- The value of `𝔾_m` on an étale `U ⟶ S` is the group of units of `Γ(U, 𝒪_U)`: the restriction
of `𝔾_m` to the small étale site is `U ↦ Γ(U, 𝒪_U)ˣ`. -/
lemma GmEtale_obj (U : S.Etale) :
    (GmEtale S).obj.obj (op U) = AddCommGrpCat.of (Additive Γ(U.left, ⊤)ˣ) :=
  rfl

/-- The value of `μ_n` on an étale `U ⟶ S` is the group of `n`-th roots of unity of
`Γ(U, 𝒪_U)`. -/
lemma muEtale_obj (n : ℕ) (U : S.Etale) :
    (muEtale S n).obj.obj (op U) = AddCommGrpCat.of (Additive (rootsOfUnity n Γ(U.left, ⊤))) :=
  rfl

/-- The restriction map of `𝔾_m` along a morphism `f : U ⟶ V` of étale `S`-schemes is the map of
units induced by `f`. -/
lemma GmEtale_map_apply {U V : S.Etale} (f : U ⟶ V) (u : Additive Γ(V.left, ⊤)ˣ) :
    (GmEtale S).obj.map f.op u =
      Additive.ofMul (Units.map f.left.appTop.hom.toMonoidHom u.toMul) :=
  (rfl)

/-- The restriction map of `μ_n` along a morphism `f : U ⟶ V` of étale `S`-schemes is the map of
`n`-th roots of unity induced by `f`. -/
lemma muEtale_map_apply (n : ℕ) {U V : S.Etale} (f : U ⟶ V)
    (u : Additive (rootsOfUnity n Γ(V.left, ⊤))) :
    (muEtale S n).obj.map f.op u =
      Additive.ofMul (restrictRootsOfUnity f.left.appTop.hom n u.toMul) :=
  (rfl)

/-- The inclusion `μ_n ⟶ 𝔾_m` on the small étale site. -/
noncomputable abbrev muToGmEtale (n : ℕ) : muEtale S n ⟶ GmEtale S :=
  (restrictSmallEtale S).map (muToGm S n)

/-- The `n`-th power map `𝔾_m ⟶ 𝔾_m`, `t ↦ tⁿ`, on the small étale site. -/
noncomputable abbrev powHomEtale (n : ℕ) : GmEtale S ⟶ GmEtale S :=
  (restrictSmallEtale S).map (powHom S n)

/-- The inclusion `μ_n ⟶ 𝔾_m` on the small étale site regards an `n`-th root of unity as a
unit. -/
lemma muToGmEtale_app_apply (n : ℕ) (U : S.Etale) (u : Additive (rootsOfUnity n Γ(U.left, ⊤))) :
    (muToGmEtale S n).hom.app (op U) u = Additive.ofMul (u.toMul : Γ(U.left, ⊤)ˣ) :=
  muToGm_app_apply S n ((Etale.forget S).obj U) u

/-- The `n`-th power map of `𝔾_m` on the small étale site sends `t` to `tⁿ`. -/
lemma powHomEtale_app_apply (n : ℕ) (U : S.Etale) (t : Additive Γ(U.left, ⊤)ˣ) :
    (powHomEtale S n).hom.app (op U) t = Additive.ofMul (t.toMul ^ n) :=
  powHom_app_apply S n ((Etale.forget S).obj U) t

/-- The inclusion `μ_n ⟶ 𝔾_m` followed by the `n`-th power map is zero. -/
@[reassoc (attr := simp)]
lemma muToGmEtale_comp_powHomEtale (n : ℕ) : muToGmEtale S n ≫ powHomEtale S n = 0 := by
  rw [← Functor.map_comp, muToGm_comp_powHom, Functor.map_zero]

/-- **`μ_n` is the kernel of the `n`-th power map on the small étale site.** -/
noncomputable def isLimitMuEtaleKernelFork (n : ℕ) :
    IsLimit (KernelFork.ofι (muToGmEtale S n) (muToGmEtale_comp_powHomEtale S n)) :=
  KernelFork.mapIsLimit _ (isLimitMuKernelFork S n) (restrictSmallEtale S)

end AlgebraicGeometry.Scheme
