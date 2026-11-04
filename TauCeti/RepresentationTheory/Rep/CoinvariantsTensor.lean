/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.RepresentationTheory.Rep.Ihom
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.CategoryTheory.Exact.KernelCokernelPair

/-!
# Change of groups, maps out of tensor coinvariants, and coefficient exactness

Let `f : G →* H` be a group homomorphism and `φ : A ⟶ Res(f)(B)` a compatible map of coefficient
representations. A morphism `v : X ⟶ Res(f)(Y)` of `G`-representations induces the linear map
`MonoidHom.coinvariantsTensorMap f φ v : (A ⊗ X)_G ⟶ (B ⊗ Y)_H` on Mathlib's tensor coinvariants,
which sends the class of `a ⊗ x` to the class of `φ a ⊗ v x`. It is natural in `X` and `Y`.

This is the degreewise construction underlying change of groups on the tensor coinvariants of
complexes, `MonoidHom.coinvariantsTensorChainMap`.

Tensor coinvariants with a projective representation are exact in the other representation
(`CategoryTheory.ShortComplex.ShortExact.map_coinvariantsTensor_projective`). For a free
representation the natural identification with finitely supported coefficient families proves
exactness. A projective representation is a retract of a free one, so the result holds without
any flatness assumption on the coefficient representations. This supplies coefficient long exact
sequences for projective-resolution computations of group homology.

For a `k`-module `N`, a `k`-linear map `X_G ⟶ N` out of the coinvariants is the same as a
morphism of representations `X ⟶ N` to the trivial representation (`Rep.coinvariantsAdjunction`);
`Rep.coinvariantsHomLinearEquiv` is the `k`-linear form of this bijection, for representations of
any monoid. For a representation `A` of a group, a morphism of representations `A ⊗ X ⟶ N` is in
turn the same as a morphism `X ⟶ Homₖ(A, N)` into the internal hom
(`Rep.MonoidalClosed.linearHomEquiv`). The composite `k`-linear equivalence is
`Rep.coinvariantsTensorHomLinearEquiv`; it sends `f` to `x ↦ (a ↦ f ⟦a ⊗ x⟧)` and is natural in
all three variables: in `X`, in `N` (postcomposition with a linear map corresponds to the induced
map of internal homs) and, contravariantly, in `A` (precomposition with the map induced by
`f : A ⟶ A'` corresponds to Mathlib's `MonoidalClosed.pre f`). It also commutes with change of
group, with precomposition by the compatible coefficient map on the internal-hom side
(`MonoidHom.coinvariantsTensorHomLinearEquiv_naturality`).

## Main definitions

* `MonoidHom.coinvariantsTensorMap`: the map `(A ⊗ X)_G ⟶ (B ⊗ Y)_H` induced by `f`, `φ`
  and `v`.
* `Rep.coinvariantsHomLinearEquiv`: `Hom(X_G, N) ≃ₗ[k] Hom_G(X, N)`.
* `Rep.coinvariantsTensorHomLinearEquiv`: `Hom((A ⊗ X)_G, N) ≃ₗ[k] Hom_G(X, Homₖ(A, N))`.

## Main results

* `MonoidHom.coinvariantsTensorMap_mk`: its value on a tensor class.
* `MonoidHom.coinvariantsTensorMap_naturality`: naturality in the representations.
* `Rep.coinvariantsTensorHomLinearEquiv_comp`: naturality of
  `Rep.coinvariantsTensorHomLinearEquiv` in the representation.
* `Rep.coinvariantsTensorHomLinearEquiv_comp_ofHom`,
  `Rep.coinvariantsTensorHomLinearEquiv_coinvariantsTensor_map_app_comp`: its naturality in the
  module and in the coefficient representation.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, §8 and Section III.2.

The tensor coinvariants functor `Rep.coinvariantsTensor` is Mathlib's construction by Amelia
Livingston.
-/

public section

noncomputable section

open CategoryTheory Rep Representation

universe u

namespace MonoidHom

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep.{u} k G} {B : Rep.{u} k H}
  (f : G →* H) (φ : A ⟶ res f B)

/-- **Change of groups on tensor coinvariants.** For `f : G →* H`, a compatible coefficient map
`φ : A ⟶ Res(f)(B)` and a morphism `v : X ⟶ Res(f)(Y)`, this is the map `(A ⊗ X)_G ⟶ (B ⊗ Y)_H`
sending the class of `a ⊗ x` to the class of `φ a ⊗ v x`. -/
def coinvariantsTensorMap {X : Rep.{u} k G} {Y : Rep.{u} k H} (v : X ⟶ res f Y) :
    ((coinvariantsTensor k G).obj A).obj X ⟶ ((coinvariantsTensor k H).obj B).obj Y :=
  ModuleCat.ofHom <| Coinvariants.lift _
    ((Coinvariants.mk _).comp (TensorProduct.map φ.hom.toLinearMap v.hom.toLinearMap))
    fun g ↦ TensorProduct.ext' fun a x ↦ by
      have h₁ := Rep.hom_comm_apply φ g a
      have h₂ := Rep.hom_comm_apply v g x
      -- The tensor representations are presented through the monoidal structure of `Rep`.
      -- State them as `Representation.tprod`, so that the tensor computation applies.
      change Coinvariants.mk (B.ρ.tprod Y.ρ) (TensorProduct.map φ.hom.toLinearMap
          v.hom.toLinearMap (A.ρ.tprod X.ρ g (a ⊗ₜ x))) =
        Coinvariants.mk (B.ρ.tprod Y.ρ)
          (TensorProduct.map φ.hom.toLinearMap v.hom.toLinearMap (a ⊗ₜ x))
      rw [tprod_apply, TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp only [IntertwiningMap.toLinearMap_apply, h₁, h₂]
      exact Coinvariants.mk_self_apply (B.ρ.tprod Y.ρ) (f g) (φ.hom a ⊗ₜ[k] v.hom x)

/-- The map sends the class of `a ⊗ x` to the class of `φ a ⊗ v x`. -/
-- Match before simplification changes the presentation of the tensor carrier.
@[simp↓]
theorem coinvariantsTensorMap_mk {X : Rep.{u} k G} {Y : Rep.{u} k H} (v : X ⟶ res f Y)
    (a : A) (x : X) :
    (f.coinvariantsTensorMap φ v).hom (coinvariantsTensorMk A X a x) =
      coinvariantsTensorMk B Y (φ.hom a) (v.hom x) :=
  (rfl)

/-- The map is natural in the representations. -/
theorem coinvariantsTensorMap_naturality {X X' : Rep.{u} k G} {Y Y' : Rep.{u} k H}
    (v : X ⟶ res f Y) (v' : X' ⟶ res f Y') (s : X ⟶ X') (t : Y ⟶ Y')
    (h : v ≫ (resFunctor f).map t = s ≫ v') :
    ((coinvariantsTensor k G).obj A).map s ≫ f.coinvariantsTensorMap φ v' =
      f.coinvariantsTensorMap φ v ≫ ((coinvariantsTensor k H).obj B).map t := by
  refine coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a x ↦ ?_)
  have hx : v'.hom (s.hom x) = t.hom (v.hom x) := (congrArg (fun w ↦ w.hom x) h).symm
  -- The functor `(coinvariantsTensor k G).obj A` acts on a tensor class through the
  -- second factor; this holds by definition of the tensor product of morphisms.
  change (f.coinvariantsTensorMap φ v').hom (coinvariantsTensorMk A X' a (s.hom x)) =
    (((coinvariantsTensor k H).obj B).map t).hom (coinvariantsTensorMk B Y (φ.hom a) (v.hom x))
  rw [coinvariantsTensorMap_mk, hx]
  rfl

end MonoidHom

namespace Rep

open MonoidalCategory

section Monoid

variable {k G : Type u} [CommRing k] [Monoid G] (N : Type u) [AddCommGroup N] [Module k N]

/-- The tensor-coinvariants functor acts on tensor classes through the second factor. -/
-- Not a simp lemma: simplification unfolds `coinvariantsTensorMk` on the left-hand side first.
theorem coinvariantsTensor_obj_map_coinvariantsTensorMk (A : Rep.{u} k G)
    {X Y : Rep.{u} k G} (f : X ⟶ Y) (a : A) (x : X) :
    (((coinvariantsTensor k G).obj A).map f).hom (coinvariantsTensorMk A X a x) =
      coinvariantsTensorMk A Y a (f.hom x) :=
  (rfl)

/-- **Maps out of coinvariants are invariant maps**: the bijection of the adjunction
`Rep.coinvariantsAdjunction` between `k`-linear maps `X_G ⟶ N` and morphisms of representations
`X ⟶ N` to the trivial representation is `k`-linear. -/
def coinvariantsHomLinearEquiv (X : Rep.{u} k G) :
    ((coinvariantsFunctor k G).obj X ⟶ ModuleCat.of k N) ≃ₗ[k] (X ⟶ Rep.trivial k G N) :=
  { (coinvariantsAdjunction k G).homEquiv X (ModuleCat.of k N) with
    map_add' _ _ := by ext; simp [Rep.add_hom, Adjunction.homEquiv_unit]
    map_smul' _ _ := by ext; simp [Rep.smul_hom, Adjunction.homEquiv_unit] }

/-- The invariant map corresponding to `f : X_G ⟶ N` is `f` composed with the projection to the
coinvariants. -/
@[simp]
theorem coinvariantsHomLinearEquiv_apply_hom_apply {X : Rep.{u} k G}
    (f : (coinvariantsFunctor k G).obj X ⟶ ModuleCat.of k N) (x : X) :
    (coinvariantsHomLinearEquiv N X f).hom x = f (Representation.Coinvariants.mk X.ρ x) :=
  (rfl)

/-- The map out of the coinvariants corresponding to `φ : X ⟶ N` sends the class of `x` to
`φ x`. -/
-- Match before simplification changes the presentation of the coinvariants carrier.
@[simp↓]
theorem coinvariantsHomLinearEquiv_symm_apply_mk {X : Rep.{u} k G} (φ : X ⟶ Rep.trivial k G N)
    (x : X) :
    (coinvariantsHomLinearEquiv N X).symm φ (Representation.Coinvariants.mk X.ρ x) = φ.hom x := by
  have h := coinvariantsHomLinearEquiv_apply_hom_apply N ((coinvariantsHomLinearEquiv N X).symm φ) x
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end Monoid

section Group

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (N : Type u) [AddCommGroup N]
  [Module k N]

/-- **Maps out of tensor coinvariants are morphisms into the internal hom**: for representations
`A` and `X` of `G` and a `k`-module `N`, the `k`-linear maps `(A ⊗ X)_G ⟶ N` correspond
`k`-linearly to the morphisms of representations `X ⟶ Homₖ(A, N)`, where `N` carries the trivial
action. The map `f` corresponds to `x ↦ (a ↦ f ⟦a ⊗ x⟧)`
(`Rep.coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply`). -/
def coinvariantsTensorHomLinearEquiv (X : Rep.{u} k G) :
    (((coinvariantsTensor k G).obj A).obj X ⟶ ModuleCat.of k N) ≃ₗ[k]
      (X ⟶ (Rep.ihom A).obj (Rep.trivial k G N)) :=
  coinvariantsHomLinearEquiv N (A ⊗ X) ≪≫ₗ MonoidalClosed.linearHomEquiv A X (Rep.trivial k G N)

variable {A N}

/-- The morphism corresponding to a map `f : (A ⊗ X)_G ⟶ N` sends `x` to `a ↦ f ⟦a ⊗ x⟧`. -/
-- Match before simplification changes the presentation of the tensor carrier.
@[simp↓]
theorem coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply {X : Rep.{u} k G}
    (f : ((coinvariantsTensor k G).obj A).obj X ⟶ ModuleCat.of k N) (x : X) (a : A) :
    -- The carrier of `Homₖ(A, N)` is `A →ₗ[k] N` only up to unfolding, so the coercion is named.
    DFunLike.coe (F := A →ₗ[k] N) ((coinvariantsTensorHomLinearEquiv A N X f).hom x) a =
      f (coinvariantsTensorMk A X a x) :=
  (rfl)

/-- The map corresponding to a morphism `φ : X ⟶ Homₖ(A, N)` sends `⟦a ⊗ x⟧` to `φ x a`. -/
-- Match before simplification changes the presentation of the tensor carrier.
@[simp↓]
theorem coinvariantsTensorHomLinearEquiv_symm_apply_coinvariantsTensorMk {X : Rep.{u} k G}
    (φ : X ⟶ (Rep.ihom A).obj (Rep.trivial k G N)) (a : A) (x : X) :
    (coinvariantsTensorHomLinearEquiv A N X).symm φ (coinvariantsTensorMk A X a x) =
      DFunLike.coe (F := A →ₗ[k] N) (φ.hom x) a := by
  have h := coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply
    ((coinvariantsTensorHomLinearEquiv A N X).symm φ) x a
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The correspondence is natural in the representation**: precomposing a map out of
`(A ⊗ X')_G` with the map induced by `g : X ⟶ X'` corresponds to precomposing with `g`. -/
theorem coinvariantsTensorHomLinearEquiv_comp {X X' : Rep.{u} k G} (g : X ⟶ X')
    (f : ((coinvariantsTensor k G).obj A).obj X' ⟶ ModuleCat.of k N) :
    coinvariantsTensorHomLinearEquiv A N X (((coinvariantsTensor k G).obj A).map g ≫ f) =
      g ≫ coinvariantsTensorHomLinearEquiv A N X' f := by
  -- `(A ⊗ -)_G` sends `g` to the map of coinvariants induced by `A ◁ g`, so this is the
  -- naturality of the hom-equivalences of the coinvariants and internal-hom adjunctions.
  change (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _
    ((coinvariantsFunctor k G).map ((tensorLeft A).map g) ≫ f)) =
      g ≫ (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _ f)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]

/-- **The correspondence is natural in the module**: postcomposing a map out of `(A ⊗ X)_G` with a
linear map `g : N →ₗ[k] N'` corresponds to postcomposing with the map `Homₖ(A, N) ⟶ Homₖ(A, N')`
induced by `g`. -/
theorem coinvariantsTensorHomLinearEquiv_comp_ofHom {N' : Type u} [AddCommGroup N']
    [Module k N'] {X : Rep.{u} k G} (f : ((coinvariantsTensor k G).obj A).obj X ⟶ ModuleCat.of k N)
    (g : N →ₗ[k] N') :
    coinvariantsTensorHomLinearEquiv A N' X (f ≫ ModuleCat.ofHom g) =
      coinvariantsTensorHomLinearEquiv A N X f ≫
        (Rep.ihom A).map ((trivialFunctor k G).map (ModuleCat.ofHom g)) := by
  -- This is the naturality of the hom-equivalences of the coinvariants and internal-hom
  -- adjunctions in their second variable; `Rep.ihom A` is the right adjoint of `A ⊗ -`.
  change (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _
    (f ≫ ModuleCat.ofHom g)) =
      (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _ f) ≫
        (ihom A).map ((trivialFunctor k G).map (ModuleCat.ofHom g))
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]

/-- **The correspondence is natural in the coefficient representation**: precomposing a map out
of `(A' ⊗ X)_G` with the map `(A ⊗ X)_G ⟶ (A' ⊗ X)_G` induced by `f : A ⟶ A'` corresponds to
postcomposing with the map `Homₖ(A', N) ⟶ Homₖ(A, N)` given by precomposition with `f`. -/
theorem coinvariantsTensorHomLinearEquiv_coinvariantsTensor_map_app_comp {A' : Rep.{u} k G}
    {X : Rep.{u} k G} (f : A ⟶ A')
    (φ : ((coinvariantsTensor k G).obj A').obj X ⟶ ModuleCat.of k N) :
    coinvariantsTensorHomLinearEquiv A N X (((coinvariantsTensor k G).map f).app X ≫ φ) =
      coinvariantsTensorHomLinearEquiv A' N X φ ≫
        (MonoidalClosed.pre f).app (Rep.trivial k G N) := by
  -- `(- ⊗ X)_G` sends `f` to the map of coinvariants induced by `f ▷ X`, so this is the
  -- naturality of the coinvariants adjunction in its first variable followed by the description
  -- of `MonoidalClosed.pre` on curried maps.
  change (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _
    ((coinvariantsFunctor k G).map (f ▷ X) ≫ φ)) =
      (ihom.adjunction A').homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _ φ) ≫
        (MonoidalClosed.pre f).app (Rep.trivial k G N)
  rw [Adjunction.homEquiv_naturality_left]
  exact (MonoidalClosed.curry_pre_app f _).symm

end Group

section Exactness

variable {k G : Type u} [CommRing k] [Group G]
  {A B : Rep.{u} k G}

/-- The free tensor-coinvariant identification is natural in the coefficient representation. -/
@[reassoc]
theorem coinvariantsTensorFreeLEquiv_naturality (f : A ⟶ B) (α : Type u)
    [DecidableEq α] :
    ((coinvariantsTensor k G).map f).app (free k G α) ≫
        (coinvariantsTensorFreeLEquiv B α).toModuleIso.hom =
      (coinvariantsTensorFreeLEquiv A α).toModuleIso.hom ≫
        ModuleCat.ofHom (Finsupp.mapRange.linearMap f.hom.toLinearMap) := by
  rw [← cancel_epi (coinvariantsTensorFreeLEquiv A α).toModuleIso.inv]
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro a
  simp [coinvariantsTensorFreeLEquiv, Representation.Coinvariants.map_mk]

end Exactness

end Rep

namespace CategoryTheory.ShortComplex.ShortExact

open Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- Tensor coinvariants with a free representation preserve short exact coefficient sequences.
There is no flatness assumption on the coefficients. -/
theorem map_coinvariantsTensor_free {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (α : Type u) :
    (S.map ((coinvariantsTensor k G).flip.obj (free k G α))).ShortExact := by
  classical
  have hinj := (Rep.mono_iff_injective S.f).mp hS.mono_f
  have hsurj := (Rep.epi_iff_surjective S.g).mp hS.epi_g
  have hex : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  let T : ShortComplex (ModuleCat k) := ShortComplex.mk
    (ModuleCat.ofHom (Finsupp.mapRange.linearMap (α := α) S.f.hom.toLinearMap))
    (ModuleCat.ofHom (Finsupp.mapRange.linearMap (α := α) S.g.hom.toLinearMap)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Finsupp.ext
      intro i
      exact congrArg (fun f : S.X₁ ⟶ S.X₃ ↦ f.hom (x i)) S.zero)
  have hT : T.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · simp [T, ShortComplex.moduleCat_exact_iff_range_eq_ker, Finsupp.ker_mapRange,
        Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.mpr hinj), hex]
    · exact (ModuleCat.mono_iff_injective _).mpr
        (Finsupp.mapRange_injective _ (map_zero _) hinj)
    · exact (ModuleCat.epi_iff_surjective _).mpr
        (Finsupp.mapRange_surjective _ (map_zero _) hsurj)
  exact (ShortComplex.shortExact_iff_of_iso (ShortComplex.isoMk
    (coinvariantsTensorFreeLEquiv S.X₁ α).toModuleIso
    (coinvariantsTensorFreeLEquiv S.X₂ α).toModuleIso
    (coinvariantsTensorFreeLEquiv S.X₃ α).toModuleIso
    (coinvariantsTensorFreeLEquiv_naturality S.f α).symm
    (coinvariantsTensorFreeLEquiv_naturality S.g α).symm)).mpr hT

/-- Tensor coinvariants with a projective representation preserve short exact sequences in the
other representation. This is the exactness needed to form coefficient connecting maps when
computing group homology from a projective resolution of the trivial representation. -/
theorem map_coinvariantsTensor_projective {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (P : Rep.{u} k G) [Projective P] :
    (S.map ((coinvariantsTensor k G).flip.obj P)).ShortExact := by
  classical
  -- Split the canonical free cover using projectivity.
  let ε : Rep.free k G P ⟶ P := Rep.freeLift k G P id
  have hε : Function.Surjective ε.hom := fun x ↦
    ⟨Finsupp.single x (MonoidAlgebra.single 1 1), by
      simp [ε, Rep.freeLift, Representation.freeLift_single_single]⟩
  have : Epi ε := (Rep.epi_iff_surjective ε).mpr hε
  let r : Retract P (Rep.free k G P) :=
    ⟨Projective.factorThru (𝟙 P) ε, ε, Projective.factorThru_comp _ _⟩
  let i := S.mapNatTrans ((coinvariantsTensor k G).flip.map r.i)
  let p := S.mapNatTrans ((coinvariantsTensor k G).flip.map r.r)
  have hip : i ≫ p = 𝟙 _ := by
    have h : (coinvariantsTensor k G).flip.map r.i ≫
        (coinvariantsTensor k G).flip.map r.r = 𝟙 _ := by
      rw [← Functor.map_comp, r.retract, Functor.map_id]
    -- `mapNatTrans` has the components of its input transformation by construction.
    ext : 1 <;> exact congrArg (fun τ ↦ τ.app _) h
  -- The coefficient sequence is a retract of the short exact free coefficient sequence.
  have hfree := hS.map_coinvariantsTensor_free P
  exact (TauCeti.IsKernelCokernelPair.of_retract
    ((TauCeti.isKernelCokernelPair_iff_shortExact _).mpr hfree) ⟨i, p, hip⟩).shortExact

end CategoryTheory.ShortComplex.ShortExact

namespace MonoidHom

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep.{u} k G} {B : Rep.{u} k H} (f : G →* H) (φ : A ⟶ res f B)
  (N : Type u) [AddCommGroup N] [Module k N]

/-- The tensor-coinvariant adjunction commutes with change of group: precomposition with the map
on tensor classes becomes precomposition with the map of representations and with `φ`. -/
theorem coinvariantsTensorHomLinearEquiv_naturality {X : Rep.{u} k G} {Y : Rep.{u} k H}
    (v : X ⟶ res f Y)
    (ℓ : ((coinvariantsTensor k H).obj B).obj Y ⟶ ModuleCat.of k N) :
    coinvariantsTensorHomLinearEquiv A N X (f.coinvariantsTensorMap φ v ≫ ℓ) =
      v ≫ (resFunctor f).map (coinvariantsTensorHomLinearEquiv B N Y ℓ) ≫
        f.ihomTrivialPrecomp N φ := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ ?_
  apply LinearMap.ext
  intro a
  -- Term-mode composition keeps the internal-hom carriers bundled while applying their
  -- pointwise API; tactic rewriting would require unfolding these carriers.
  exact (coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply
    (f.coinvariantsTensorMap φ v ≫ ℓ) x a).trans <|
    (congrArg ℓ (f.coinvariantsTensorMap_mk φ v a x)).trans <|
      ((f.ihomTrivialPrecomp_hom_apply N φ
        ((coinvariantsTensorHomLinearEquiv B N Y ℓ).hom (v.hom x)) a).trans
          (coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply ℓ (v.hom x) (φ.hom a))).symm

end MonoidHom
