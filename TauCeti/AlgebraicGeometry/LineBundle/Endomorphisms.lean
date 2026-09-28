/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
# Endomorphisms and automorphisms of an invertible sheaf

Let `M` be an invertible sheaf on a scheme `X`. Every endomorphism of `M` is multiplication by a
unique global function: the ring homomorphism `Γ(X, 𝒪_X) →+* End M` sending a global function to
the scalar multiplication it induces on sections
(`AlgebraicGeometry.Scheme.Modules.globalSectionsAction`) is bijective. Consequently the
automorphism group of `M` is the unit group `Γ(X, 𝒪_X)ˣ` of the global functions.

The proof is local. Over an open `V` carrying a rank-one trivialization `t` of `M`, an
endomorphism `φ` acts on the basis section `e_t` by a regular function `r_t`, its *trivialization
scalar*, and then acts as multiplication by the restriction of `r_t` on the sections of `M` over
every open subset of `V`. The scalars attached to two trivializations agree on the intersection of
their domains, so they glue to a global function `r` with `φ = r • 𝟙`. Uniqueness is the fact
that a global function is determined by its restrictions to a cover and is read off from its
action on a basis section.

The bijection is the statement that a line bundle has no automorphisms other than the global units.
It is the input for rigidifying line bundles along a section `x₀ : S → X` of `f : X → S`: a
trivialization along `x₀` fixes the pullback to `S` of every automorphism, so no nontrivial
automorphism survives once the restriction `Γ(X, 𝒪_X)ˣ → Γ(S, 𝒪_S)ˣ` along `x₀` is injective, for
instance when `f_* 𝒪_X = 𝒪_S`. Without that injectivity the units in the kernel of the restriction
still act on the rigidified bundle.

## Main declarations

* `Scheme.Modules.Hom.trivializationScalar`: the regular function by which an endomorphism acts on
  the basis section of a rank-one trivialization, with
  `Scheme.Modules.Hom.app_eq_trivializationScalar_smul` describing the action on all sections over
  open subsets of the trivializing open, and
  `Scheme.Modules.Hom.map_trivializationScalar_eq` comparing two trivializations on their common
  domain;
* `Scheme.Modules.globalSectionsAction_bijective`: for an invertible sheaf, the action of global
  functions on the sheaf is a bijection onto its endomorphisms;
* `Scheme.Modules.globalSectionsActionRingEquiv`: the ring isomorphism `Γ(X, 𝒪_X) ≃+* End M`;
* `Scheme.Modules.unitsGlobalSectionsMulEquivAut`: the group isomorphism `Γ(X, 𝒪_X)ˣ ≃* Aut M`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 5 and Exercise II.5.1(d)
  (`𝓗om(ℒ, ℒ) ≅ 𝒪_X` for an invertible sheaf).
* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} {M : X.Modules}

section TrivializationScalar

variable {V : X.Opens} (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)

/-- The regular function on `V` by which an endomorphism `φ` of `M` acts on the basis section of
a rank-one trivialization `t` of `M` over `V`: the coordinate of `φ` applied to that basis
section. -/
def Hom.trivializationScalar (φ : M ⟶ M) : Γ(X, V) :=
  trivializationCoordinate M t (𝟙 V) (φ.app V (trivializationGenerator M t))

/-- An endomorphism of `M` multiplies the basis section of a rank-one trivialization by its
trivialization scalar. -/
@[simp]
theorem Hom.app_trivializationGenerator (φ : M ⟶ M) :
    φ.app V (trivializationGenerator M t) =
      φ.trivializationScalar t • trivializationGenerator M t := by
  have h := eq_trivializationCoordinate_smul_map_trivializationGenerator M t (𝟙 V)
    (φ.app V (trivializationGenerator M t))
  rwa [op_id, M.presheaf.map_id, ConcreteCategory.id_apply] at h

/-- On every open subset `W` of the domain `V` of a rank-one trivialization, an endomorphism of
`M` acts on sections as multiplication by the restriction of its trivialization scalar. -/
theorem Hom.app_eq_trivializationScalar_smul (φ : M ⟶ M) {W : X.Opens} (i : W ⟶ V)
    (s : Γ(M, W)) :
    φ.app W s = X.presheaf.map i.op (φ.trivializationScalar t) • s := by
  have hs := eq_trivializationCoordinate_smul_map_trivializationGenerator M t i s
  have hnat : φ.app W (M.presheaf.map i.op (trivializationGenerator M t)) =
      M.presheaf.map i.op (φ.app V (trivializationGenerator M t)) := by
    simpa only [mapPresheaf_app, unop_op] using
      φ.mapPresheaf.naturality_apply i.op (trivializationGenerator M t)
  calc φ.app W s
      = φ.app W (trivializationCoordinate M t i s •
          M.presheaf.map i.op (trivializationGenerator M t)) := by rw [← hs]
    _ = trivializationCoordinate M t i s • X.presheaf.map i.op (φ.trivializationScalar t) •
          M.presheaf.map i.op (trivializationGenerator M t) := by
        rw [Hom.app_smul, hnat, Hom.app_trivializationGenerator, Modules.map_smul]
    _ = X.presheaf.map i.op (φ.trivializationScalar t) • s := by
        rw [smul_smul, mul_comm, ← smul_smul, ← hs]

/-- The trivialization scalars of an endomorphism for two rank-one trivializations agree on any
common open subset of their domains. -/
theorem Hom.map_trivializationScalar_eq (φ : M ⟶ M) {V₁ V₂ W : X.Opens}
    (t₁ : SheafOfModules.free (R := X.ringCatSheaf.over V₁) PUnit ≅ M.over V₁)
    (t₂ : SheafOfModules.free (R := X.ringCatSheaf.over V₂) PUnit ≅ M.over V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) :
    X.presheaf.map i₁.op (φ.trivializationScalar t₁) =
      X.presheaf.map i₂.op (φ.trivializationScalar t₂) := by
  have h := (φ.app_eq_trivializationScalar_smul t₁ i₁
    (M.presheaf.map i₁.op (trivializationGenerator M t₁))).symm.trans
      (φ.app_eq_trivializationScalar_smul t₂ i₂
        (M.presheaf.map i₁.op (trivializationGenerator M t₁)))
  have h' := congrArg (trivializationCoordinate M t₁ i₁) h
  simpa only [LinearEquiv.map_smul, trivializationCoordinate_map_trivializationGenerator,
    smul_eq_mul, mul_one] using h'

/-- The trivialization scalar of multiplication by a global function is the restriction of that
function to the trivializing open. -/
@[simp]
theorem Hom.trivializationScalar_globalSectionsSmul (r : Γ(X, ⊤)) :
    (globalSectionsSmul M r).trivializationScalar t = X.presheaf.map V.leTop.op r := by
  simp only [Hom.trivializationScalar, globalSectionsSmul_app, smul_apply, LinearEquiv.map_smul,
    trivializationCoordinate_trivializationGenerator, smul_eq_mul, mul_one]

end TrivializationScalar

section Invertible

variable (M) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]

/-- Distinct global functions act differently on an invertible sheaf. -/
theorem globalSectionsAction_injective : Function.Injective (globalSectionsAction M) := by
  intro r s hrs
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  have hcover : (⊤ : X.Opens) ≤ iSup t.X :=
    ((Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop).iSup_eq_top.ge
  apply X.sheaf.eq_of_locally_eq' t.X ⊤ (fun i ↦ (t.X i).leTop) hcover
  intro i
  have h := congrArg (fun ψ : End M ↦ trivializationCoordinate M (t.iso i) (𝟙 (t.X i))
    (ψ.app (t.X i) (trivializationGenerator M (t.iso i)))) hrs
  have key : X.presheaf.map (t.X i).leTop.op r = X.presheaf.map (t.X i).leTop.op s := by
    simpa only [globalSectionsAction_apply, globalSectionsSmul_app, smul_apply,
      LinearEquiv.map_smul, trivializationCoordinate_trivializationGenerator, smul_eq_mul,
      mul_one] using h
  exact key

/-- Every endomorphism of an invertible sheaf is multiplication by a global function. -/
theorem globalSectionsAction_surjective : Function.Surjective (globalSectionsAction M) := by
  intro φ
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  have hcover : (⊤ : X.Opens) ≤ iSup t.X :=
    ((Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop).iSup_eq_top.ge
  -- The trivialization scalars of `φ` are compatible, hence glue to a global function `r`.
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf t.X
      fun i ↦ φ.trivializationScalar (t.iso i) := fun i j ↦
    φ.map_trivializationScalar_eq (t.iso i) (t.iso j) (Opens.infLELeft _ _) (Opens.infLERight _ _)
  have key : ∃ r : Γ(X, ⊤), ∀ i, X.presheaf.map (t.X i).leTop.op r =
      φ.trivializationScalar (t.iso i) := by
    obtain ⟨r, hr, -⟩ :=
      X.sheaf.existsUnique_gluing' t.X ⊤ (fun i ↦ (t.X i).leTop) hcover _ hcompat
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := key
  refine ⟨r, ?_⟩
  rw [globalSectionsAction_apply]
  refine Modules.hom_ext _ _ fun U ↦ ?_
  ext x
  rw [globalSectionsSmul_app, smul_apply]
  -- Both sides are sections of `M` over `U`; compare them on the cover `U ⊓ t.X i` of `U`.
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i ↦ U ⊓ t.X i) U (fun i ↦ homOfLE inf_le_left)
  · rw [← inf_iSup_eq]
    exact le_inf le_rfl (le_top.trans hcover)
  · intro i
    have hnat : M.presheaf.map (homOfLE inf_le_left : U ⊓ t.X i ⟶ U).op (φ.app U x) =
        φ.app (U ⊓ t.X i) (M.presheaf.map (homOfLE inf_le_left).op x) := by
      simpa only [mapPresheaf_app, unop_op] using
        (φ.mapPresheaf.naturality_apply (homOfLE inf_le_left : U ⊓ t.X i ⟶ U).op x).symm
    -- Restricting the global function `r` in two steps is restricting it in one.
    have hglobal {V W : X.Opens} (j : W ⟶ V) :
        X.presheaf.map j.op (X.presheaf.map V.leTop.op r) = X.presheaf.map W.leTop.op r := by
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
      rfl
    rw [Modules.map_smul, hnat,
      φ.app_eq_trivializationScalar_smul (t.iso i) (homOfLE inf_le_right), ← hr i, hglobal,
      hglobal]

/-- For an invertible sheaf, the action of global functions is a bijection onto the
endomorphisms of the sheaf. -/
theorem globalSectionsAction_bijective : Function.Bijective (globalSectionsAction M) :=
  ⟨globalSectionsAction_injective M, globalSectionsAction_surjective M⟩

/-- Every endomorphism of an invertible sheaf is multiplication by a unique global function. -/
theorem existsUnique_globalSectionsSmul_eq (φ : M ⟶ M) :
    ∃! r : Γ(X, ⊤), globalSectionsSmul M r = φ := by
  simpa only [globalSectionsAction_apply] using (globalSectionsAction_bijective M).existsUnique φ

/-- **Endomorphisms of a line bundle are global functions.** For an invertible sheaf `M` on a
scheme `X`, the action of global functions is a ring isomorphism `Γ(X, 𝒪_X) ≃+* End M`. -/
def globalSectionsActionRingEquiv : Γ(X, ⊤) ≃+* End M :=
  RingEquiv.ofBijective _ (globalSectionsAction_bijective M)

@[simp]
lemma globalSectionsActionRingEquiv_apply (r : Γ(X, ⊤)) :
    globalSectionsActionRingEquiv M r = globalSectionsSmul M r := by
  rw [globalSectionsActionRingEquiv, RingEquiv.ofBijective_apply, globalSectionsAction_apply]

@[simp]
lemma globalSectionsSmul_globalSectionsActionRingEquiv_symm (φ : M ⟶ M) :
    globalSectionsSmul M ((globalSectionsActionRingEquiv M).symm φ) = φ := by
  rw [← globalSectionsActionRingEquiv_apply, RingEquiv.apply_symm_apply]

/-- **Automorphisms of a line bundle are global units.** For an invertible sheaf `M` on a scheme
`X`, the action of global functions is a group isomorphism `Γ(X, 𝒪_X)ˣ ≃* Aut M`. -/
def unitsGlobalSectionsMulEquivAut : Γ(X, ⊤)ˣ ≃* Aut M :=
  (Units.mapEquiv (globalSectionsActionRingEquiv M).toMulEquiv).trans (Aut.unitsEndEquivAut M)

-- The next two `rfl` steps unfold `Units.mapEquiv` and `Aut.unitsEndEquivAut`, which have no
-- component lemmas: the automorphism attached to a unit `u` has `hom` and `inv` the images of
-- `u` and `u⁻¹` under the ring isomorphism.
@[simp]
lemma unitsGlobalSectionsMulEquivAut_apply_hom (u : Γ(X, ⊤)ˣ) :
    (unitsGlobalSectionsMulEquivAut M u).hom = globalSectionsSmul M u := by
  have h : (unitsGlobalSectionsMulEquivAut M u).hom = globalSectionsActionRingEquiv M u := rfl
  rw [h, globalSectionsActionRingEquiv_apply]

@[simp]
lemma unitsGlobalSectionsMulEquivAut_apply_inv (u : Γ(X, ⊤)ˣ) :
    (unitsGlobalSectionsMulEquivAut M u).inv = globalSectionsSmul M ↑u⁻¹ := by
  have h : (unitsGlobalSectionsMulEquivAut M u).inv = globalSectionsActionRingEquiv M ↑u⁻¹ := rfl
  rw [h, globalSectionsActionRingEquiv_apply]

/-- An automorphism of an invertible sheaf is multiplication by the global unit corresponding to
it. -/
@[simp]
lemma globalSectionsSmul_unitsGlobalSectionsMulEquivAut_symm (f : Aut M) :
    globalSectionsSmul M ((unitsGlobalSectionsMulEquivAut M).symm f) = f.hom := by
  rw [← unitsGlobalSectionsMulEquivAut_apply_hom, MulEquiv.apply_symm_apply]

end Invertible

end

end AlgebraicGeometry.Scheme.Modules
