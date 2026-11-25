/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Corestrict.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
import Mathlib.Algebra.Module.ULift
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Finite
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.RegularSubcomodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Surjective coalgebra maps and subquotients of corestricted comodules

Let `f : C →ₗc[k] D` be a morphism of coalgebras over a field `k`. Corestriction along `f` turns
finite right `C`-comodules into finite right `D`-comodules. This file proves that `f` is surjective
exactly when every finite `D`-comodule `M` is a subquotient of a corestricted one: there are a
finite `C`-comodule `Y`, a finite `D`-comodule `Z`, a monomorphism `Z ⟶ corestrict f Y` and an
epimorphism `Z ⟶ M` in `FGComoduleCat k D`.

For commutative Hopf algebras, `f : 𝒪(G') → 𝒪(G)` is the coordinate map of a homomorphism of
affine group schemes `G → G'`, and corestriction along `f` restricts representations of `G'` to
`G`. Since `G → G'` is a closed immersion exactly when `f` is surjective
(`TauCeti.CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff`), the theorem is the closed-immersion
criterion: `G → G'` is a closed immersion exactly when every finite-dimensional representation of
`G` is a subquotient of the restriction of a finite-dimensional representation of `G'`.

## Main results

* `CoalgHom.surjective_of_forall_exists_mono_epi`: if every finite `D`-comodule is a subquotient of
  a corestricted finite `C`-comodule, then `f` is surjective.
* `CoalgHom.exists_mono_epi_of_surjective`: conversely, if `f` is surjective, every finite
  `D`-comodule is such a subquotient.
* `CoalgHom.surjective_iff_forall_exists_mono_epi`: the resulting characterization.

## Implementation notes

For the first direction, an element `d : D` lies in a finite-dimensional subcoalgebra `E`, and `d`
is the matrix coefficient of the counit at `d` in the regular comodule `E`. Pulling this
coefficient back along the epimorphism and extending it along the monomorphism shows that `d` is a
coefficient of a corestricted comodule, hence lies in the range of `f`. Finite-dimensional
witnesses are transported to lifted finite coordinate spaces, so the coalgebras may have
independent universes and the common carrier universe need only contain that of `k`.

For the converse, the coaction embeds `M` into the cofree `D`-comodule `M ⊗ D`, which is the image
of the corestricted cofree `C`-comodule `M ⊗ C` under `id ⊗ f`. Since `M` is finite, its image in
`M ⊗ D` is already covered by a finite `C`-subcomodule `Y ≤ M ⊗ C`. The image `Q` of `Y` is a
finite `D`-comodule containing `M`, and the pullback of `Y ↠ Q ↩ M` in the abelian category
`FGComoduleCat k D` is the required subquotient.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, in *Hodge cycles, motives, and Shimura
  varieties*, Lecture Notes in Math. 900, 1982, Proposition 2.21(b).
* M. E. Sweedler, *Hopf Algebras*, Chapter 2, for corestriction, cofree comodules and the
  fundamental theorem of coalgebras.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

open TauCeti

namespace CoalgHom

universe u v w x

section Surjective

variable {k : Type u} [Field k]

/-- If every finite comodule over `D` is a subquotient of the corestriction along `f` of a finite
comodule over `C`, then `f` is surjective. -/
theorem surjective_of_forall_exists_mono_epi {C : Type v} {D : Type w} [AddCommGroup C]
    [Module k C] [Coalgebra k C] [AddCommGroup D] [Module k D] [Coalgebra k D] (f : C →ₗc[k] D)
    (h : ∀ M : FGComoduleCat.{u, w, max u x} k D, ∃ (Y : FGComoduleCat.{u, v, max u x} k C)
      (Z : FGComoduleCat.{u, w, max u x} k D) (i : Z ⟶ (FGComoduleCat.corestrict f).obj Y)
      (p : Z ⟶ M), Mono i ∧ Epi p) :
    Function.Surjective f := by
  intro d
  -- `d` is a coefficient of the finite regular comodule of a subcoalgebra containing it.
  obtain ⟨E, hE, hdE⟩ := Subcoalgebra.exists_finiteDimensional_subcoalgebra_mem (k := k) d
  let N := E.toRegularSubcomodule
  have : Module.Finite k N := inferInstanceAs (Module.Finite k E.toRegularSubcomodule.toSubmodule)
  let e : N ≃ₗ[k] ULift.{x} (Fin (Module.finrank k N) → k) :=
    (Module.finBasis k N).equivFun.trans ULift.moduleEquiv.symm
  let _ := Comodule.Transport (C := D) e
  obtain ⟨Y, Z, i, p, hi, hp⟩ := h (FGComoduleCat.of (ULift.{x} (Fin (Module.finrank k N) → k)))
  have hp' : Function.Surjective p := (ModuleCat.epi_iff_surjective _).1
    ((forget₂ (FGComoduleCat.{u, w, max u x} k D) (ModuleCat.{max u x} k)).map_epi p)
  have hi' : Function.Injective i := (ModuleCat.mono_iff_injective _).1
    ((forget₂ (FGComoduleCat.{u, w, max u x} k D) (ModuleCat.{max u x} k)).map_mono i)
  obtain ⟨z, hz⟩ := hp' (e ⟨d, hdE⟩)
  -- Extend the pulled-back counit functional from `Z` to the corestriction of `Y`.
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective i.hom.toLinearMap
    (LinearMap.ker_eq_bot.2 hi')
  let φ : ULift.{x} (Fin (Module.finrank k N) → k) →ₗ[k] k :=
    Coalgebra.counit (R := k) (A := D) ∘ₗ SMulMemClass.subtype N ∘ₗ e.symm.toLinearMap
  obtain ⟨c, hc⟩ := f.matrixCoefficient_corestrict_mem_range Y
    (φ ∘ₗ p.hom.toLinearMap ∘ₗ r) (i z)
  refine ⟨c, hc.trans ?_⟩
  calc Comodule.matrixCoefficient (C := D) (φ ∘ₗ p.hom.toLinearMap ∘ₗ r) (i.hom z)
      = Comodule.matrixCoefficient (C := D) ((φ ∘ₗ p.hom.toLinearMap ∘ₗ r) ∘ₗ i.hom.toLinearMap)
          z := Comodule.matrixCoefficient_map i.hom _ z
    _ = Comodule.matrixCoefficient (C := D) (φ ∘ₗ p.hom.toLinearMap) z := by
      congr 1
      exact LinearMap.ext fun x ↦ congrArg (φ ∘ₗ p.hom.toLinearMap) (LinearMap.congr_fun hr x)
    _ = Comodule.matrixCoefficient (C := D) φ (p z) :=
      (Comodule.matrixCoefficient_map p.hom φ z).symm
    _ = d := by
      rw [hz]
      rw [← Comodule.transportToHom_apply (C := D) e, Comodule.matrixCoefficient_map]
      simpa only [φ, Comodule.transportToHom_toLinearMap, LinearMap.comp_assoc,
        LinearEquiv.symm_comp, LinearMap.comp_id] using
        Comodule.matrixCoefficient_counit_comp_subtype N ⟨d, hdE⟩

attribute [local instance] Comodule.cofree in
/-- A finite cofree image containing the coaction gives the quotient used in the proof. -/
private theorem exists_epi_mono_of_coact_mem_range {C : Type v} {D : Type w}
    [AddCommGroup C] [Module k C] [Coalgebra k C]
    [AddCommGroup D] [Module k D] [Coalgebra k D] (f : C →ₗc[k] D)
    (M : FGComoduleCat.{u, w, max u x} k D) (Y : FGComoduleCat.{u, v, max u x} k C)
    (G : Comodule.Hom k D ((FGComoduleCat.corestrict f).obj Y) (M ⊗[k] D))
    (hρ : ∀ m : M, Comodule.coact (R := k) (C := D) (M := M) m ∈ Comodule.Hom.range G) :
    ∃ (Q : FGComoduleCat.{u, w, max u x} k D)
      (q : (FGComoduleCat.corestrict f).obj Y ⟶ Q) (j : M ⟶ Q), Epi q ∧ Mono j := by
  -- Transport the finite image to the same carrier universe before taking the pullback.
  let Q := Comodule.Hom.range G
  have : Module.Finite k Q := G.range_finite
  let _ : AddCommGroup Q := Module.addCommMonoidToAddCommGroup k
  let eQ : Q ≃ₗ[k] ULift.{x} (Fin (Module.finrank k Q) → k) :=
    (Module.finBasis k Q).equivFun.trans ULift.moduleEquiv.symm
  let Q' : FGComoduleCat.{u, w, max u x} k D :=
    ⟨ComoduleCat.transport k D eQ, Module.Finite.equiv eQ⟩
  let _ := Comodule.Transport (C := D) eQ
  let q : (FGComoduleCat.corestrict f).obj Y ⟶ Q' :=
    ObjectProperty.homMk ((Comodule.transportToHom eQ).comp (G.codRestrict Q G.mem_range_self))
  let j : M ⟶ Q' := ObjectProperty.homMk
    ((Comodule.transportToHom eQ).comp ((Comodule.Hom.cofreeUnit M).codRestrict Q hρ))
  have hq : Epi q := by
    apply (forget₂ (FGComoduleCat.{u, w, max u x} k D) (ModuleCat.{max u x} k)).epi_of_epi_map
    apply (ModuleCat.epi_iff_surjective _).2
    have hs : Function.Surjective (G.codRestrict Q G.mem_range_self) := by
      rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := Comodule.Hom.mem_range.1 hz
      exact ⟨y, Subtype.ext (Comodule.Hom.codRestrict_apply G Q G.mem_range_self y)⟩
    -- Forgetting the wrappers leaves the composite comodule map.
    have : Function.Surjective
        ((Comodule.transportToHom eQ).comp (G.codRestrict Q G.mem_range_self)) := by
      intro z
      obtain ⟨y, hy⟩ := hs (eQ.symm z)
      exact ⟨y, by simp only [Comodule.Hom.comp_apply, Comodule.transportToHom_apply,
        hy, LinearEquiv.apply_symm_apply]⟩
    exact this
  have hj : Mono j := by
    apply (forget₂ (FGComoduleCat.{u, w, max u x} k D) (ModuleCat.{max u x} k)).mono_of_mono_map
    apply (ModuleCat.mono_iff_injective _).2
    have hi : Function.Injective ((Comodule.Hom.cofreeUnit M).codRestrict Q hρ) := by
      intro m m' h
      have h' := congrArg (fun z : Q ↦ z.val) h
      have he := Comodule.Hom.codRestrict_apply (Comodule.Hom.cofreeUnit M) Q hρ
      rw [he, he] at h'
      exact Comodule.coact_injective h'
    -- Forgetting the wrappers leaves the composite comodule map.
    have : Function.Injective ((Comodule.transportToHom eQ).comp
        ((Comodule.Hom.cofreeUnit M).codRestrict Q hρ)) := by
      intro m m' h
      apply hi
      apply eQ.injective
      simpa only [Comodule.Hom.comp_apply, Comodule.transportToHom_apply] using h
    exact this
  exact ⟨Q', q, j, hq, hj⟩

attribute [local instance] Comodule.cofree in
/-- If `f` is surjective, every finite comodule `M` over `D` embeds into a quotient of the
corestriction along `f` of a finite comodule over `C`. -/
private theorem exists_epi_mono_of_surjective {C : Type v} {D : Type w}
    [AddCommGroup C] [Module k C]
    [Coalgebra k C] [AddCommGroup D] [Module k D] [Coalgebra k D] (f : C →ₗc[k] D)
    (hf : Function.Surjective f) (M : FGComoduleCat.{u, w, max u x} k D) :
    ∃ (Y : FGComoduleCat.{u, v, max u x} k C) (Q : FGComoduleCat.{u, w, max u x} k D)
      (q : (FGComoduleCat.corestrict f).obj Y ⟶ Q) (j : M ⟶ Q), Epi q ∧ Mono j := by
  let _ : Comodule k D (M ⊗[k] C) := Comodule.Corestrict f
  let g := Comodule.Hom.cofreeLTensor M f
  -- A linear section of the surjection `id ⊗ f : M ⊗ C → M ⊗ D`.
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective g.toLinearMap
    (by
      rw [LinearMap.range_eq_top, Comodule.Hom.cofreeLTensor_toLinearMap]
      exact LinearMap.lTensor_surjective M hf)
  -- A finite `C`-subcomodule `Y ≤ M ⊗ C` whose image under `id ⊗ f` contains the coaction of `M`.
  obtain ⟨Ys, hYs, hPY⟩ := Subcomodule.exists_finite_subcomodule_of_fg (R := k) (C := C)
    (LinearMap.range (σ ∘ₗ Comodule.coact (R := k) (C := D) (M := M)))
    (by rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _)
  have : Module.Finite k Ys := hYs
  let _ : AddCommGroup Ys := Module.addCommMonoidToAddCommGroup k
  let eY : Ys ≃ₗ[k] ULift.{x} (Fin (Module.finrank k Ys) → k) :=
    (Module.finBasis k Ys).equivFun.trans ULift.moduleEquiv.symm
  let _ := Comodule.Transport (C := C) eY
  let Y : FGComoduleCat.{u, v, max u x} k C :=
    ⟨ComoduleCat.transport k C eY, Module.Finite.equiv eY⟩
  let F : Comodule.Hom k C Y (M ⊗[k] C) :=
    (Subcomodule.subtype Ys).comp (Comodule.transportInvHom (C := C) eY)
  let G : Comodule.Hom k D ((FGComoduleCat.corestrict f).obj Y) (M ⊗[k] D) :=
    g.comp (Comodule.corestrictHom (M := Y) f F)
  have hG : G.toLinearMap = g.toLinearMap ∘ₗ SMulMemClass.subtype Ys ∘ₗ eY.symm.toLinearMap := by
    -- The bundled corestriction supplies the source instances; reduce its exposed wrappers.
    change g.toLinearMap ∘ₗ (Subcomodule.subtype Ys).toLinearMap ∘ₗ
      (Comodule.transportInvHom (C := C) eY).toLinearMap = _
    rw [Subcomodule.subtype_toLinearMap, Comodule.transportInvHom_toLinearMap]
  have hρ (m : M) : Comodule.coact (R := k) (C := D) (M := M) m ∈ Comodule.Hom.range G := by
    rw [← Subcomodule.mem_toSubmodule, Comodule.Hom.range_toSubmodule, hG]
    refine ⟨eY ⟨_, hPY ⟨m, rfl⟩⟩, ?_⟩
    -- Evaluate the linear composite before simplifying the inverse coordinate map.
    change g.toLinearMap (eY.symm (eY ⟨_, _⟩)).val = _
    rw [eY.symm_apply_apply]
    exact LinearMap.congr_fun hσ (Comodule.coact (R := k) (C := D) (M := M) m)
  obtain ⟨Q, q, j, hq, hj⟩ := exists_epi_mono_of_coact_mem_range f M Y G hρ
  exact ⟨Y, Q, q, j, hq, hj⟩

/-- If `f` is surjective, every finite comodule over `D` is a subquotient of the corestriction
along `f` of a finite comodule over `C`. -/
theorem exists_mono_epi_of_surjective {C : Type v} {D : Type w} [AddCommGroup C] [Module k C]
    [Coalgebra k C] [AddCommGroup D] [Module k D] [Coalgebra k D] (f : C →ₗc[k] D)
    (hf : Function.Surjective f) (M : FGComoduleCat.{u, w, max u x} k D) :
    ∃ (Y : FGComoduleCat.{u, v, max u x} k C) (Z : FGComoduleCat.{u, w, max u x} k D)
      (i : Z ⟶ (FGComoduleCat.corestrict f).obj Y) (p : Z ⟶ M), Mono i ∧ Epi p := by
  obtain ⟨Y, Q, q, j, hq, hj⟩ := exists_epi_mono_of_surjective f hf M
  -- In the abelian category of finite `D`-comodules, a subobject of a quotient is a quotient of a
  -- subobject: pull back the epimorphism `q` along the monomorphism `j`.
  exact ⟨Y, pullback q j, pullback.fst q j, pullback.snd q j, inferInstance, inferInstance⟩

/-- A morphism of coalgebras over a field is surjective exactly when every finite comodule over
`D` is a subquotient of the corestriction along `f` of a finite comodule over `C`. -/
theorem surjective_iff_forall_exists_mono_epi {C : Type v} {D : Type w}
    [AddCommGroup C] [Module k C] [Coalgebra k C]
    [AddCommGroup D] [Module k D] [Coalgebra k D] (f : C →ₗc[k] D) :
    Function.Surjective f ↔ ∀ M : FGComoduleCat.{u, w, max u x} k D,
      ∃ (Y : FGComoduleCat.{u, v, max u x} k C) (Z : FGComoduleCat.{u, w, max u x} k D)
        (i : Z ⟶ (FGComoduleCat.corestrict f).obj Y) (p : Z ⟶ M), Mono i ∧ Epi p :=
  ⟨exists_mono_epi_of_surjective f, surjective_of_forall_exists_mono_epi f⟩

end Surjective

end CoalgHom
