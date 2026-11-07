/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.RingTheory.Etale.Splitting
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Relative
import TauCeti.RingTheory.TotallySplit

/-!
# Splitting finite étale schemes over a field

Every finite étale scheme over a field becomes the spectrum of a finite product of `n` copies
of the base field after a finite Galois extension whose degree divides `n!`. The isomorphism
is over the extended base, so it labels all points as rational points, including their scheme
structures.
The empty scheme corresponds to the product indexed by `Fin 0`.

This is the scheme form of `TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct`, transported
through `TauCeti.FiniteEtaleScheme.spec` and Mathlib's affine pullback comparison. Two finite étale
schemes split over a common finite Galois extension, one splitting their disjoint union.

Once a finite étale scheme `S` and a flat `S`-scheme `E` of constant rank `d` are both
split over the base field, `E` is `d` copies of `S`
(`AlgebraicGeometry.Scheme.Hom.exists_split_of_finrank_eq`): the rational points of `E` above
each rational point of `S` are counted by the rank
(`Algebra.IsFiniteSplit.nonempty_algEquiv_fun_of_rankAtStalk_eq`).

Counted in the functor-of-points sense, there is a finite Galois extension `L / K` of degree
dividing `n!` over which a finite étale scheme `X` of rank `n` over `K` has exactly `n` points
with values in `L`, that is `n` morphisms `Spec L ⟶ X` over `Spec K`. The rank is Mathlib's
`AlgebraicGeometry.Scheme.Hom.finrank`, so this applies to any finite étale scheme over a field
whose rank is known.

## References

* The Stacks Project, Tag 03QR (schemes étale over a point).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite étale scheme becomes a disjoint union of `n` rational points after a finite
Galois field extension of degree dividing `n!`. The splitting is an isomorphism over the
extended base. -/
theorem exists_split_of_isFinite_of_etale {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L) (n : ℕ),
      Module.finrank K L ∣ n.factorial ∧
        Nonempty (Over.mk (pullback.snd f (Spec.algebraMap K L)) ≅
          Over.mk (Spec.algebraMap L (Fin n → L))) := by
  obtain ⟨A, ⟨e₀⟩⟩ := f.exists_finiteEtale_algebra
  obtain ⟨L, _, _, _, _, hdeg, hL⟩ :=
    TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct K A.obj
  obtain ⟨n, ⟨a⟩⟩ := hL.nonempty_algEquiv_fun
  have hn : Module.finrank K A.obj = n := by
    rw [← Module.finrank_baseChange (R := L), a.toLinearEquiv.finrank_eq]
    simp
  let e₁ :=
    TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv K A.obj L (Fin n → L) a
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, hn ▸ hdeg,
    ⟨((Over.pullback (Spec.algebraMap K L)).mapIso e₀).symm ≪≫ e₁⟩⟩

/-- Two finite étale schemes over a field become disjoint unions of `n` and `m` rational points
after one common finite Galois field extension. The splittings are isomorphisms over the extended
base. -/
theorem exists_split_of_isFinite_of_etale₂ {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) [IsFinite f] [Etale f] [IsFinite g]
    [Etale g] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L) (n m : ℕ),
        Nonempty (Over.mk (pullback.snd f (Spec.algebraMap K L)) ≅
          Over.mk (Spec.algebraMap L (Fin n → L))) ∧
        Nonempty (Over.mk (pullback.snd g (Spec.algebraMap K L)) ≅
          Over.mk (Spec.algebraMap L (Fin m → L))) := by
  obtain ⟨A, ⟨eA⟩⟩ := f.exists_finiteEtale_algebra
  obtain ⟨B, ⟨eB⟩⟩ := g.exists_finiteEtale_algebra
  obtain ⟨L, _, _, _, _, -, _⟩ :=
    TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct K (A.obj × B.obj)
  -- Both factors of the split algebra `L ⊗[K] (A × B)` are split.
  have : Algebra.IsFiniteSplit L (L ⊗[K] A.obj) := .of_surjective
    (Algebra.TensorProduct.map (AlgHom.id L L) (AlgHom.fst K A.obj B.obj))
    (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id Prod.fst_surjective)
  have : Algebra.IsFiniteSplit L (L ⊗[K] B.obj) := .of_surjective
    (Algebra.TensorProduct.map (AlgHom.id L L) (AlgHom.snd K A.obj B.obj))
    (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id Prod.snd_surjective)
  obtain ⟨n, ⟨a⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun L (L ⊗[K] A.obj)
  obtain ⟨m, ⟨b⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun L (L ⊗[K] B.obj)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, m,
    ⟨((Over.pullback (Spec.algebraMap K L)).mapIso eA).symm ≪≫
      TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv K A.obj L (Fin n → L) a⟩,
    ⟨((Over.pullback (Spec.algebraMap K L)).mapIso eB).symm ≪≫
      TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv K B.obj L (Fin m → L) b⟩⟩

/-- **A flat morphism of constant rank between split schemes over a field is a trivial cover.**
Let `p : E ⟶ S` be flat of rank `d` at every point, where `S` and `E` are identified with
`Spec (Fin n → L)` and `Spec (Fin m → L)` compatibly with their morphisms to `Spec L`; such a
`p` is automatically finite. Then `E` is `Spec (Fin d → Fin n → L)` over `S`, that is, `d`
copies of `S`. -/
theorem exists_split_of_finrank_eq {L : Type u} [Field L] {S E : Scheme.{u}} {n m d : ℕ}
    (p : E ⟶ S) [Flat p] (hp : ∀ s, p.finrank s = d)
    (e : S ≅ Spec (.of (Fin n → L))) (eE : E ≅ Spec (.of (Fin m → L)))
    (h : eE.hom ≫ Spec.algebraMap L (Fin m → L) = p ≫ e.hom ≫ Spec.algebraMap L (Fin n → L)) :
    ∃ e' : E ≅ Spec (.of (Fin d → Fin n → L)),
      e'.hom ≫ Spec.algebraMap (Fin n → L) (Fin d → Fin n → L) = p ≫ e.hom := by
  -- On the split models, `p` is the spectrum of an `L`-algebra map, which makes `Fin m → L` a
  -- finite flat algebra of constant rank `d` over `Fin n → L`.
  let p₀ := eE.inv ≫ p ≫ e.hom
  have hp₀ : p₀ ≫ Spec.algebraMap L (Fin n → L) = Spec.algebraMap L (Fin m → L) := by
    simp only [p₀, Category.assoc, ← h, Iso.inv_hom_id_assoc]
  have hφ : CommRingCat.ofHom (algebraMap L (Fin n → L)) ≫ Spec.preimage p₀ =
      CommRingCat.ofHom (algebraMap L (Fin m → L)) :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, hp₀])
  let φ : (Fin n → L) →ₐ[L] (Fin m → L) :=
    { (Spec.preimage p₀).hom with
      commutes' r := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hφ) r }
  let : Algebra (Fin n → L) (Fin m → L) := φ.toAlgebra
  have : IsScalarTower L (Fin n → L) (Fin m → L) := .of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have hφp : Spec.map (CommRingCat.ofHom (algebraMap (Fin n → L) (Fin m → L))) = p₀ :=
    Spec.map_preimage p₀
  have : Module.Finite (Fin n → L) (Fin m → L) := .of_restrictScalars_finite L _ _
  -- `p` is finite, being `p₀` up to isomorphisms.
  have : IsFinite p := by
    have : IsFinite p₀ := by
      rw [← hφp, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
      infer_instance
    rw [show p = eE.hom ≫ p₀ ≫ e.inv by simp [p₀]]
    infer_instance
  have : Module.Flat (Fin n → L) (Fin m → L) := by
    have : Flat p₀ := by dsimp only [p₀]; infer_instance
    rwa [← hφp, Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff] at this
  have hrank (q : PrimeSpectrum (Fin n → L)) :
      Module.rankAtStalk (R := Fin n → L) (Fin m → L) q = d := by
    have hsq : IsPullback (𝟙 _) (p ≫ e.hom) p e.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
    rw [← finrank_SpecMap_algebraMap, hφp]
    exact (congrFun (finrank_comp_left_of_isIso eE.inv (p ≫ e.hom)) q).trans <|
      (finrank_of_isPullback _ _ _ _ hsq q).trans (hp _)
  -- Hence `Fin m → L` is the trivial cover `Fin d → (Fin n → L)` of `Fin n → L`.
  obtain ⟨ψ⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun_of_rankAtStalk_eq (K := L) hrank
  refine ⟨eE ≪≫ Scheme.Spec.mapIso ψ.toRingEquiv.toCommRingCatIso.symm.op, ?_⟩
  have hψ : CommRingCat.ofHom (algebraMap (Fin n → L) (Fin d → Fin n → L)) ≫
      ψ.toRingEquiv.toCommRingCatIso.inv =
        CommRingCat.ofHom (algebraMap (Fin n → L) (Fin m → L)) :=
    CommRingCat.hom_ext (RingHom.ext ψ.symm.commutes)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Category.assoc,
    Spec.algebraMap, ← Spec.map_comp, Iso.symm_hom, Quiver.Hom.unop_op, hψ, hφp, p₀,
    Iso.hom_inv_id_assoc]

/-- **A finite étale scheme of rank `n` has `n` points over a Galois extension of degree dividing
`n!`.** For a finite étale morphism `f : X ⟶ Spec K` of rank `n` there is a finite Galois
extension `L / K` of degree dividing `n!` such that exactly `n` morphisms `Spec L ⟶ X` lie over
`Spec K`. -/
theorem exists_natCard_hom_eq_finrank_of_isFinite_of_etale {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] (s : Spec (.of K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L),
      Module.finrank K L ∣ (f.finrank s).factorial ∧
        Nat.card (Over.mk (Spec.algebraMap K L) ⟶ Over.mk f) = f.finrank s := by
  obtain ⟨A, ⟨e⟩⟩ := f.exists_finiteEtale_algebra
  have : Module.Finite K A.obj := Algebra.FormallyUnramified.finite_of_free K A.obj
  -- The rank of `f` is the dimension of its coordinate algebra `A`.
  have hrank : f.finrank s = Module.finrank K A.obj := by
    have hw : e.hom.left ≫ f = Spec.algebraMap K A.obj := Over.w e.hom
    rw [← Scheme.Hom.finrank_comp_left_of_isIso e.hom.left f, hw, Spec.algebraMap]
    exact (Scheme.Hom.finrank_SpecMap_algebraMap K A.obj s).trans
      (congrFun Module.rankAtStalk_eq_finrank_of_free s)
  obtain ⟨L, _, _, _, _, hdeg, hL⟩ :=
    TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct K A.obj
  -- `L ⊗[K] A` is split over `L`, so `A` has `finrank K A` characters with values in `L`.
  have hcard : Nat.card (A.obj →ₐ[K] L) = Module.finrank K A.obj := by
    rw [Nat.card_congr (AlgHom.liftEquiv K L A.obj L), hL.card_algHom_eq_finrank,
      Module.finrank_baseChange]
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    by rw [hrank]; exact hdeg, ?_⟩
  rw [hrank, ← hcard]
  -- The points of `X` with values in `L` are the characters of `A` with values in `L`.
  let eL : Over.mk (Spec.algebraMap K L) ≅ (algSpec (.of K)).obj (op (CommAlgCat.of K L)) :=
    (TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk (R := .of K) (.of K L)).symm
  let eA : Over.mk (Spec.algebraMap K A.obj) ≅
      (algSpec (.of K)).obj (op (CommAlgCat.of K A.obj)) :=
    (TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk (R := .of K) (.of K A.obj)).symm
  exact Nat.card_congr ((Iso.homCongr eL (e.symm ≪≫ eA)).trans
    (TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom _ _))

end AlgebraicGeometry.Scheme.Hom
