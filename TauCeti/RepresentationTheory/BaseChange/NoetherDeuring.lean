/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.RepresentationTheory.Semisimple

/-!
# Intertwiners under free scalar extension, and descent of isomorphisms

Let `ρ` and `σ` be representations of a monoid `G` over a commutative ring `K`, with `ρ` on a
finite projective `K`-module, and let `L` be a commutative `K`-algebra that is free as a
`K`-module (for instance any field extension of a field `K`). Then scalar extension commutes
with the space of intertwining maps:

```text
L ⊗[K] Hom_G(V, W) ≃ Hom_G(L ⊗[K] V, L ⊗[K] W)
```

(`Representation.intertwiningMapBaseChangeEquivOfFree`). Unlike
`Representation.intertwiningMapBaseChangeEquiv`, the monoid `G` need not be finite. Writing an
`L`-linear map `L ⊗ V → L ⊗ W` in a `K`-basis `(bᵢ)` of `L` as `∑ bᵢ ⊗ fᵢ` with `fᵢ : V → W`, it
intertwines the base-changed actions exactly when every coefficient `fᵢ` intertwines `ρ` and `σ`,
because the coefficients of `g`-translates are the `g`-translates of the coefficients.

Over a field `K`, the dimension of every intertwiner space is therefore unchanged by any nonzero
commutative `K`-algebra `L` (`Representation.finrank_intertwiningMap_baseChange_of_free`). Since
semisimple representations are determined by such dimensions
(`Representation.nonempty_equiv_of_finrank_intertwiningMap_eq`), two finite-dimensional
semisimple representations over `K` that become equivalent over `L` are already equivalent over
`K` (`Representation.nonempty_equiv_of_nonempty_equiv_baseChange`). This is the
Noether–Deuring theorem for semisimple representations, in the form used to descend the
Brauer–Nesbitt theorem from an algebraic closure of `K` to `K`: `V ≅ W` over `K` if and only
if `AlgebraicClosure K ⊗ V ≅ AlgebraicClosure K ⊗ W`.

## Main results

* `Representation.intertwiningMapBaseChangeEquivOfFree`: free scalar extension commutes with
  intertwiner spaces, for any monoid.
* `Representation.finrank_intertwiningMap_baseChange_of_free`: intertwiner dimensions over a field
  are unchanged by scalar extension.
* `Representation.nonempty_equiv_of_nonempty_equiv_baseChange`: **Noether–Deuring for semisimple
  representations.** Semisimple representations that are equivalent after scalar extension are
  equivalent.
* `Representation.nonempty_equiv_baseChange_iff`: the same as an equivalence of statements.
* `TauCeti.ContinuousRep.nonempty_iso_of_nonempty_equiv_baseChange`: the same for continuous
  representations with their module topologies.

## References

* C. W. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*,
  Theorem 29.7 (Noether–Deuring).
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, proof of Proposition 2.6.
-/

public section

open TensorProduct

namespace Representation

section Intertwiner

variable {K L G V W : Type*} [CommRing K] [CommRing L] [Algebra K L] [Monoid G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The underlying linear map of an intertwining map, as a `K`-linear map. -/
private def toLinearMapₗ (ρ : Representation K G V) (σ : Representation K G W) :
    IntertwiningMap ρ σ →ₗ[K] V →ₗ[K] W where
  toFun f := f.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The intertwining defect `h ↦ σ g ∘ h - h ∘ ρ g` of a linear map at `g`. -/
private def defect (ρ : Representation K G V) (σ : Representation K G W) (g : G) :
    (V →ₗ[K] W) →ₗ[K] V →ₗ[K] W :=
  LinearMap.llcomp K V W W (σ g) - LinearMap.lcomp K W (ρ g)

private theorem defect_apply (ρ : Representation K G V) (σ : Representation K G W) (g : G)
    (h : V →ₗ[K] W) : defect ρ σ g h = σ g ∘ₗ h - h ∘ₗ ρ g :=
  rfl

variable [Module.Projective K V] [Module.Finite K V]

/-- The identification `L ⊗[K] Hom_K(V, W) ≃ Hom_L(L ⊗ V, L ⊗ W)` carries the scalar extension
of the intertwining defect at `g` to the intertwining defect of the base-changed actions. -/
private theorem baseChangeHom_equiv_lTensor_defect (ρ : Representation K G V)
    (σ : Representation K G W) (g : G) (x : L ⊗[K] (V →ₗ[K] W)) :
    (LinearMap.isBaseChange_baseChangeHom K L V W).equiv ((defect ρ σ g).lTensor L x) =
      baseChange L σ g ∘ₗ (LinearMap.isBaseChange_baseChangeHom K L V W).equiv x -
        (LinearMap.isBaseChange_baseChangeHom K L V W).equiv x ∘ₗ baseChange L ρ g := by
  induction x with
  | tmul a h =>
    simp only [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, LinearMap.baseChangeHom_apply,
      defect_apply, LinearMap.baseChange_sub, LinearMap.baseChange_comp, baseChange_apply,
      LinearMap.comp_smul, LinearMap.smul_comp]
    exact smul_sub a (_ : L ⊗[K] V →ₗ[L] L ⊗[K] W) _
  | add x y hx hy =>
    simp only [map_add, hx, hy, LinearMap.comp_add, LinearMap.add_comp]
    abel

/-- Scalar extension of intertwining maps, `a ⊗ f ↦ a • (L ⊗ f)`, as an `L`-linear map. -/
private noncomputable def intertwiningMapBaseChangeHom (ρ : Representation K G V)
    (σ : Representation K G W) :
    L ⊗[K] IntertwiningMap ρ σ →ₗ[L] IntertwiningMap (baseChange L ρ) (baseChange L σ) where
  toFun x :=
    { toLinearMap := (LinearMap.isBaseChange_baseChangeHom K L V W).equiv
        ((toLinearMapₗ ρ σ).baseChange L x)
      isIntertwining' g := by
        have h0 : defect ρ σ g ∘ₗ toLinearMapₗ ρ σ = 0 := LinearMap.ext fun f => by
          simpa [defect_apply, toLinearMapₗ, sub_eq_zero] using (f.isIntertwining' g).symm
        refine (sub_eq_zero.mp ?_).symm
        rw [← baseChangeHom_equiv_lTensor_defect, LinearMap.baseChange_eq_lTensor,
          ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero,
          LinearMap.zero_apply, map_zero] }
  map_add' x y := IntertwiningMap.ext (by simp)
  map_smul' a x := IntertwiningMap.ext (by simp)

private theorem toLinearMap_intertwiningMapBaseChangeHom (ρ : Representation K G V)
    (σ : Representation K G W) (x : L ⊗[K] IntertwiningMap ρ σ) :
    (intertwiningMapBaseChangeHom ρ σ x).toLinearMap =
      (LinearMap.isBaseChange_baseChangeHom K L V W).equiv
        ((toLinearMapₗ ρ σ).baseChange L x) :=
  rfl

variable [Module.Free K L]

private theorem intertwiningMapBaseChangeHom_bijective (ρ : Representation K G V)
    (σ : Representation K G W) :
    Function.Bijective (intertwiningMapBaseChangeHom (L := L) ρ σ) := by
  set e := (LinearMap.isBaseChange_baseChangeHom K L V W).equiv
  refine ⟨fun x y hxy => ?_, fun F => ?_⟩
  · have h := congrArg IntertwiningMap.toLinearMap hxy
    rw [toLinearMap_intertwiningMapBaseChangeHom, toLinearMap_intertwiningMapBaseChangeHom,
      e.injective.eq_iff, LinearMap.baseChange_eq_lTensor] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (fun f g hfg => IntertwiningMap.ext hfg) h
  · -- Expand `F` in a `K`-basis of `L`; every coefficient intertwines `ρ` and `σ`.
    classical
    let b := Module.Free.chooseBasis K L
    let c := equivFinsuppOfBasisLeft (N := V →ₗ[K] W) b
    set x := e.symm F.toLinearMap
    have hcoeff (i : Module.Free.ChooseBasisIndex K L) (g : G) :
        c x i ∘ₗ ρ g = σ g ∘ₗ c x i := by
      have h0 : (defect ρ σ g).lTensor L x = 0 := by
        apply e.injective
        rw [baseChangeHom_equiv_lTensor_defect, LinearEquiv.apply_symm_apply, map_zero,
          F.isIntertwining']
        exact sub_self (_ : L ⊗[K] V →ₗ[L] L ⊗[K] W)
      have := b.equivFinsuppOfBasisLeft_lTensor_apply (defect ρ σ g) x i
      rw [h0, map_zero, Finsupp.zero_apply, defect_apply] at this
      exact (sub_eq_zero.mp this.symm).symm
    let f (i : Module.Free.ChooseBasisIndex K L) : IntertwiningMap ρ σ := ⟨c x i, hcoeff i⟩
    refine ⟨∑ i ∈ (c x).support, b i ⊗ₜ[K] f i, IntertwiningMap.ext ?_⟩
    rw [toLinearMap_intertwiningMapBaseChangeHom, ← e.eq_symm_apply, map_sum]
    have hx : x = c.symm (c x) := (c.symm_apply_apply x).symm
    change _ = x
    conv_rhs => rw [hx, equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum]
    rfl

/-- **Free scalar extension commutes with intertwiner spaces.** For representations `ρ` and `σ`
of a monoid over a commutative ring `K`, with `ρ` on a finite projective module, and a
commutative `K`-algebra `L` that is free over `K`, the map `a ⊗ f ↦ a • (L ⊗ f)` identifies
`L ⊗[K] Hom_G(ρ, σ)` with the intertwining maps between the base changes. The monoid need not
be finite: an `L`-linear map is intertwining exactly when each of its coefficients in a `K`-basis
of `L` is. -/
noncomputable def intertwiningMapBaseChangeEquivOfFree (ρ : Representation K G V)
    (σ : Representation K G W) :
    L ⊗[K] IntertwiningMap ρ σ ≃ₗ[L] IntertwiningMap (baseChange L ρ) (baseChange L σ) :=
  LinearEquiv.ofBijective _ (intertwiningMapBaseChangeHom_bijective ρ σ)

/-- Scalar extension of the intertwiner space sends a pure tensor to the corresponding scalar
multiple of the base-changed intertwining map. -/
@[simp]
theorem intertwiningMapBaseChangeEquivOfFree_tmul (ρ : Representation K G V)
    (σ : Representation K G W) (a : L) (f : IntertwiningMap ρ σ) :
    intertwiningMapBaseChangeEquivOfFree ρ σ (a ⊗ₜ[K] f) = a • f.baseChange L := by
  refine IntertwiningMap.ext ?_
  simp [intertwiningMapBaseChangeEquivOfFree, toLinearMap_intertwiningMapBaseChangeHom,
    toLinearMapₗ, IsBaseChange.equiv_tmul]

end Intertwiner

section Field

variable {K L G V W : Type*} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] [Monoid G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]

/-- **Intertwiner dimensions are unchanged by scalar extension.** For representations of any
monoid over a field `K`, with finite-dimensional source, and a nonzero commutative `K`-algebra
`L`, the intertwiner space of the base changes has the same dimension over `L` as the original
one over `K`. -/
theorem finrank_intertwiningMap_baseChange_of_free (ρ : Representation K G V)
    (σ : Representation K G W) :
    Module.finrank L (IntertwiningMap (baseChange L ρ) (baseChange L σ)) =
      Module.finrank K (IntertwiningMap ρ σ) := by
  rw [← (intertwiningMapBaseChangeEquivOfFree ρ σ).finrank_eq, Module.finrank_baseChange]

omit [FiniteDimensional K V] in
/-- An equivalence after scalar extension preserves the dimensions of intertwiner spaces from any
finite-dimensional representation. -/
private theorem finrank_intertwiningMap_eq_of_equiv_baseChange {U : Type*} [AddCommGroup U]
    [Module K U] [FiniteDimensional K U] (τ : Representation K G U) {ρ : Representation K G V}
    {σ : Representation K G W} (e : (baseChange L ρ).Equiv (baseChange L σ)) :
    Module.finrank K (IntertwiningMap τ ρ) = Module.finrank K (IntertwiningMap τ σ) := by
  rw [← finrank_intertwiningMap_baseChange_of_free (L := L),
    ← finrank_intertwiningMap_baseChange_of_free (L := L)]
  exact (Equiv.intertwiningMapCongr (Equiv.refl _) e).finrank_eq

variable [FiniteDimensional K W]

/-- **Noether–Deuring for semisimple representations.** Two finite-dimensional semisimple
representations of a monoid over a field `K` that become equivalent after extending scalars to a
nonzero commutative `K`-algebra `L` (for instance an algebraic closure of `K`) are already
equivalent over `K`. Their intertwiner dimensions from every irreducible subrepresentation agree,
since they agree after scalar extension. -/
theorem nonempty_equiv_of_nonempty_equiv_baseChange (ρ : Representation K G V)
    (σ : Representation K G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : Nonempty ((baseChange L ρ).Equiv (baseChange L σ))) : Nonempty (ρ.Equiv σ) :=
  have ⟨e⟩ := h
  nonempty_equiv_of_finrank_intertwiningMap_eq ρ σ
    (fun _ _ => finrank_intertwiningMap_eq_of_equiv_baseChange _ e)
    (fun _ _ => finrank_intertwiningMap_eq_of_equiv_baseChange _ e)

/-- Two finite-dimensional semisimple representations over a field `K` are equivalent if and only
if they are equivalent after extending scalars to a nonzero commutative `K`-algebra. -/
theorem nonempty_equiv_baseChange_iff (ρ : Representation K G V) (σ : Representation K G W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation] :
    Nonempty ((baseChange L ρ).Equiv (baseChange L σ)) ↔ Nonempty (ρ.Equiv σ) :=
  ⟨nonempty_equiv_of_nonempty_equiv_baseChange ρ σ, fun ⟨e⟩ => ⟨e.baseChange L⟩⟩

end Field

end Representation

namespace TauCeti.ContinuousRep

variable {Γ K L V W : Type*} [Monoid Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
  [CommRing L] [Nontrivial L] [Algebra K L]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
  [IsModuleTopology K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [TopologicalSpace W] [IsModuleTopology K W]

/-- **Noether–Deuring for continuous representations.** Two jointly continuous finite-dimensional
semisimple representations over a topological field `K`, with their module topologies, whose
underlying representations become equivalent after extending scalars to a nonzero commutative
`K`-algebra, are isomorphic as continuous representations. -/
theorem nonempty_iso_of_nonempty_equiv_baseChange (ρ : ContinuousRep Γ K V)
    (σ : ContinuousRep Γ K W) [ρ.toRepresentation.IsSemisimpleRepresentation]
    [σ.toRepresentation.IsSemisimpleRepresentation]
    (h : Nonempty ((ρ.toRepresentation.baseChange L).Equiv (σ.toRepresentation.baseChange L))) :
    Nonempty (Iso ρ σ) :=
  (Representation.nonempty_equiv_of_nonempty_equiv_baseChange _ _ h).map Iso.ofEquiv

end TauCeti.ContinuousRep
