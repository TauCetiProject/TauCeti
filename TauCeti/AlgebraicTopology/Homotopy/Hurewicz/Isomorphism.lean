/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Cubical
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.HomotopyClass
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction
public import TauCeti.Topology.Homotopy.HomotopyGroup.Basic

/-!
# The cubical Hurewicz isomorphism

Let `X` be `(m - 1)`-connected at `x`, in the sense that `πₖ(X, x)` is trivial for every
`k < m`. Eilenberg's coherent deformation retracts the normalized cubical chains of `X` onto
the chains spanned by `m`-based cubes. In degree `m`, these cubes are precisely generalized
loops. The face relation identifies the resulting quotient by boundaries with `πₘ(X, x)`.

This file carries out that last step when `m ≥ 2`. Retraction onto based cubes proves
surjectivity, while applying the based-cube class map to a bounding chain proves injectivity.
The resulting bijection is packaged as an additive equivalence.

The inductive Hurewicz criterion
`TauCeti.subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex` shows
that a simply connected space with vanishing integral normalized cubical homology in degrees
at least two has trivial homotopy groups in every degree.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407--447.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.32.
-/

public section

noncomputable section

open CategoryTheory TauCeti
open scoped unitInterval Topology Topology.Homotopy

namespace HomotopyGroup

variable {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}

private abbrev K (X : Type) [TopologicalSpace X] :=
  (normalizedCubicalChainComplex ℤ).obj (TopCat.of X)

private abbrev chainEquiv : (K X).X n ≃ₗ[ℤ] NormalizedCubicalChain X ℤ n :=
  normalizedCubicalChainComplexXEquiv (TopCat.of X) n

private abbrev chainOf (g : NormalizedCubicalChain X ℤ n) : (K X).X n :=
  chainEquiv.symm g

private abbrev chainTo (g : (K X).X n) : NormalizedCubicalChain X ℤ n :=
  chainEquiv g

private theorem chainTo_chainOf (g : NormalizedCubicalChain X ℤ n) :
    chainTo (chainOf g) = g :=
  chainEquiv.apply_symm_apply g

private theorem chainOf_chainTo (g : (K X).X n) :
    chainOf (chainTo g) = g :=
  chainEquiv.symm_apply_apply g

private theorem boundary_eq_zero_of_mem_basedSpan
    {g : NormalizedCubicalChain X ℤ (n + 2)}
    (hg : g ∈ Submodule.span ℤ
      (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x})) :
    NormalizedCubicalChain.boundary X ℤ (n + 1) g = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨c, hc, rfl⟩ := hg
      let p : Ω^ (Fin (n + 2)) X x :=
        ⟨c, SingularCube.isBased_iff_mem_genLoop.1 hc⟩
      exact GenLoop.boundary_ofCube_eq_zero ℤ p
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul r a _ ha => simp [ha]

private def basedCycle (g : NormalizedCubicalChain X ℤ (n + 2))
    (hg : g ∈ Submodule.span ℤ
      (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x})) :
    (K X).cycles (n + 2) :=
  (K X).moduleCatCyclesMk (chainOf g) (n + 1) (by simp)
    (by
      apply chainEquiv.injective
      calc
        chainTo ((K X).d (n + 2) (n + 1) (chainOf g)) =
            NormalizedCubicalChain.boundary X ℤ (n + 1) (chainTo (chainOf g)) :=
          normalizedCubicalChainComplexXEquiv_d_apply (TopCat.of X) (n + 1) (chainOf g)
        _ = NormalizedCubicalChain.boundary X ℤ (n + 1) g := by rw [chainTo_chainOf]
        _ = 0 := boundary_eq_zero_of_mem_basedSpan hg
        _ = chainTo 0 := (map_zero chainEquiv).symm)

private theorem iCycles_basedCycle (g : NormalizedCubicalChain X ℤ (n + 2))
    (hg : g ∈ Submodule.span ℤ
      (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x})) :
    chainTo ((K X).iCycles (n + 2) (basedCycle g hg)) = g := by
  calc
    chainTo ((K X).iCycles (n + 2) (basedCycle g hg)) = chainTo (chainOf g) :=
      congrArg chainTo ((K X).iCycles_moduleCatCyclesMk (n + 2) (chainOf g)
        (n + 1) (by simp) _)
    _ = g := chainTo_chainOf g

private theorem basedCycle_add
    (a b : NormalizedCubicalChain X ℤ (n + 2))
    (ha : a ∈ Submodule.span ℤ
      (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x}))
    (hb : b ∈ Submodule.span ℤ
      (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x})) :
    basedCycle (a + b) (Submodule.add_mem _ ha hb) = basedCycle a ha + basedCycle b hb := by
  apply (K X).moduleCat_iCycles_injective
  apply chainEquiv.injective
  simp only [map_add, iCycles_basedCycle]

private theorem basedCycle_smul
    (r : ℤ) (a : NormalizedCubicalChain X ℤ (n + 2))
    (ha : a ∈ Submodule.span ℤ
      (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x})) :
    basedCycle (r • a) (Submodule.smul_mem _ r ha) = r • basedCycle a ha := by
  apply (K X).moduleCat_iCycles_injective
  apply chainEquiv.injective
  simp only [map_zsmul, iCycles_basedCycle]

/-- The cubical Hurewicz homomorphism sends the class of a generalized loop to the cubical
Hurewicz class of that loop. -/
private theorem cubicalHurewiczHom_ofMul_mk (p : Ω^ (Fin (n + 2)) X x) :
    cubicalHurewiczHom ℤ (n + 1)
        (Additive.ofMul (α := HomotopyGroup (Fin (n + 2)) X x) ⟦p⟧) =
      GenLoop.cubicalHurewicz ℤ p :=
  -- `toMul_ofMul` cannot be used by `rw` here: `⟦p⟧` is elaborated at the quotient type
  -- underlying `HomotopyGroup`, so the step is the definitional equation `toMul (ofMul a) = a`.
  (cubicalHurewiczHom_apply ℤ (n + 1) _).trans (cubicalHurewicz_mk ℤ (n + 1) p)

private theorem cubicalHurewiczHom_basedClassHom
    (g : NormalizedCubicalChain X ℤ (n + 2))
    (hg : g ∈ Submodule.span ℤ
      (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x})) :
    cubicalHurewiczHom ℤ (n + 1) (NormalizedCubicalChain.basedClassHom x n g) =
      (K X).homologyπ (n + 2) (basedCycle g hg) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨c, hc, rfl⟩ := hg
      let p : Ω^ (Fin (n + 2)) X x :=
        ⟨c, SingularCube.isBased_iff_mem_genLoop.1 hc⟩
      have hbc : NormalizedCubicalChain.basedClassHom x n
          (NormalizedCubicalChain.ofCube X ℤ c) =
          Additive.ofMul (α := HomotopyGroup (Fin (n + 2)) X x) ⟦p⟧ := by
        simpa only [p] using
          NormalizedCubicalChain.basedClassHom_ofCube_of_isBased hc
      rw [hbc, cubicalHurewiczHom_ofMul_mk]
      exact (GenLoop.homologyπ_eq_cubicalHurewicz ℤ p (by
        apply (@chainEquiv X _ (n + 2)).injective
        calc
          chainTo ((K X).iCycles (n + 2)
              (basedCycle (NormalizedCubicalChain.ofCube X ℤ c)
                (Submodule.subset_span ⟨c, hc, rfl⟩))) =
              NormalizedCubicalChain.ofCube X ℤ c :=
            iCycles_basedCycle _ _
          _ = chainTo (chainOf (NormalizedCubicalChain.ofCube X ℤ c)) :=
            (chainTo_chainOf _).symm)).symm
  | zero =>
      have hzero : (0 : NormalizedCubicalChain X ℤ (n + 2)) ∈ Submodule.span ℤ
          (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x}) :=
        Submodule.zero_mem _
      have hz : basedCycle (x := x) (0 : NormalizedCubicalChain X ℤ (n + 2)) hzero = 0 := by
        apply (K X).moduleCat_iCycles_injective
        rw [map_zero]
        apply chainEquiv.injective
        exact (iCycles_basedCycle 0 hzero).trans (map_zero chainEquiv).symm
      simp [hz]
  | add a b ha hb hha hhb =>
      rw [map_add, map_add, hha, hhb, basedCycle_add a b ha hb]
      exact (map_add _ _ _).symm
  | smul r a ha hha =>
      rw [map_smul, map_zsmul, hha, basedCycle_smul r a ha]
      exact (map_zsmul _ _ _).symm

private theorem cubicalHurewiczHom_surjective
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    : Function.Surjective (cubicalHurewiczHom (X := X) (x := x) ℤ (n + 1)) := by
  intro a
  obtain ⟨z, rfl⟩ := (K X).moduleCat_homologyπ_surjective (n + 2) a
  let D := basedCubeDeformation hX
  let g : NormalizedCubicalChain X ℤ (n + 2) :=
    D.retractChain ℤ (n + 2) (chainTo ((K X).iCycles (n + 2) z))
  have hg : g ∈ Submodule.span ℤ
      (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x}) :=
    D.retractChain_mem_span ℤ _
  refine ⟨NormalizedCubicalChain.basedClassHom x n g, ?_⟩
  rw [cubicalHurewiczHom_basedClassHom g hg]
  have hcycle : basedCycle g hg =
      HomologicalComplex.cyclesMap (D.retractChainMap ℤ) (n + 2) z := by
    apply (K X).moduleCat_iCycles_injective
    apply chainEquiv.injective
    refine (iCycles_basedCycle g hg).trans ?_
    rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
    exact (D.normalizedCubicalChainComplexXEquiv_retractChainMap_f_apply ℤ (n + 2)
      ((K X).iCycles (n + 2) z)).symm
  rw [hcycle]
  calc
    (K X).homologyπ (n + 2)
        (HomologicalComplex.cyclesMap (D.retractChainMap ℤ) (n + 2) z) =
        HomologicalComplex.homologyMap (D.retractChainMap ℤ) (n + 2)
          ((K X).homologyπ (n + 2) z) := by
            simpa only [ModuleCat.comp_apply] using
              (ConcreteCategory.congr_hom
                (HomologicalComplex.homologyπ_naturality (D.retractChainMap ℤ) (n + 2)) z).symm
    _ = (K X).homologyπ (n + 2) z := by
      have hm := Homotopy.homologyMap_eq
        (BasedCubeDeformation.retractHomotopy (X := TopCat.of X) (n := n + 2) (x := x) D ℤ)
        (n + 2)
      simpa only [HomologicalComplex.homologyMap_id, ModuleCat.id_apply] using
        (ConcreteCategory.congr_hom hm ((K X).homologyπ (n + 2) z)).symm

private theorem cubicalHurewiczHom_injective
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Function.Injective (cubicalHurewiczHom (X := X) (x := x) ℤ (n + 1)) := by
  suffices hzero : ∀ a, cubicalHurewiczHom ℤ (n + 1) a = 0 → a = 0 by
    intro a b hab
    rw [← sub_eq_zero]
    apply hzero (a - b)
    rw [map_sub, hab, sub_self]
  intro a ha
  induction a using Additive.rec with
  | ofMul q =>
    induction q using Quotient.inductionOn with
    | _ p =>
      let p' : Ω^ (Fin (n + 2)) X x := p
      rw [cubicalHurewiczHom_ofMul_mk] at ha
      have hp : SingularCube.IsBased (n + 2) x p'.1 :=
        SingularCube.isBased_iff_mem_genLoop.2 p'.2
      let g := NormalizedCubicalChain.ofCube X ℤ p'.1
      have hg : g ∈ Submodule.span ℤ
          (NormalizedCubicalChain.ofCube X ℤ '' {c | c.IsBased (n + 2) x}) :=
        Submodule.subset_span ⟨p', hp, rfl⟩
      rw [← GenLoop.homologyπ_eq_cubicalHurewicz ℤ p' (by
        apply (@chainEquiv X _ (n + 2)).injective
        exact (iCycles_basedCycle g hg).trans (chainTo_chainOf g).symm)] at ha
      obtain ⟨b, hb⟩ := ((K X).moduleCat_homologyπ_eq_zero_iff (m := n + 3) (by simp)
        (basedCycle g hg)).1 ha
      have hboundary : NormalizedCubicalChain.boundary X ℤ (n + 2) (chainTo b) = g := by
        have hi := congrArg (fun z ↦ (K X).iCycles (n + 2) z) hb
        have hi' := congrArg chainTo hi
        calc
          NormalizedCubicalChain.boundary X ℤ (n + 2) (chainTo b) =
              chainTo ((K X).d (n + 3) (n + 2) b) :=
            (normalizedCubicalChainComplexXEquiv_d_apply (TopCat.of X) (n + 2) b).symm
          _ = chainTo ((K X).iCycles (n + 2)
                ((K X).toCycles (n + 3) (n + 2) b)) := by
            exact congrArg chainTo
              (ConcreteCategory.congr_hom
                (HomologicalComplex.toCycles_i (K X) (n + 3) (n + 2)) b).symm
          _ = g := by
            exact hi'.trans (iCycles_basedCycle g hg)
      let D := basedCubeDeformation hX
      have hclass : NormalizedCubicalChain.basedClassHom x n g = 0 := by
        calc
          NormalizedCubicalChain.basedClassHom x n g =
              NormalizedCubicalChain.basedClassHom x n
                (D.retractChain ℤ (n + 2) g) := by
                  simp only [g, D.retractChain_ofCube, D.retract_of_isBased hp]
          _ = NormalizedCubicalChain.basedClassHom x n
                (D.retractChain ℤ (n + 2)
                  (NormalizedCubicalChain.boundary X ℤ (n + 2) (chainTo b))) := by
                    rw [hboundary]
          _ = NormalizedCubicalChain.basedClassHom x n
                (NormalizedCubicalChain.boundary X ℤ (n + 2)
                  (D.retractChain ℤ (n + 3) (chainTo b))) := by
                    rw [D.boundary_retractChain]
          _ = 0 := NormalizedCubicalChain.basedClassHom_boundary_of_mem_span
            (D.retractChain_mem_span ℤ (chainTo b))
      simpa only [g, NormalizedCubicalChain.basedClassHom_ofCube,
        SingularCube.basedClass_coe, p'] using hclass

/-- **The cubical Hurewicz isomorphism.** If `πₖ(X, x)` is trivial for every `k < n + 2`, then
the degree-`n + 2` cubical Hurewicz homomorphism is an additive equivalence from `π_{n+2}(X, x)`
to normalized cubical homology. -/
def cubicalHurewiczAddEquiv
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Additive (HomotopyGroup (Fin (n + 2)) X x) ≃+
      ((normalizedCubicalChainComplex ℤ).obj (TopCat.of X)).homology (n + 2) :=
  AddEquiv.ofBijective (cubicalHurewiczHom ℤ (n + 1))
    ⟨cubicalHurewiczHom_injective hX, cubicalHurewiczHom_surjective hX⟩

/-- The cubical Hurewicz equivalence has the cubical Hurewicz homomorphism as its forward map. -/
@[simp]
theorem cubicalHurewiczAddEquiv_apply
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    cubicalHurewiczAddEquiv hX a = cubicalHurewiczHom ℤ (n + 1) a := by
  exact AddEquiv.ofBijective_apply _ _ _

end HomotopyGroup

namespace TauCeti

open HomotopyGroup CategoryTheory.Limits

variable {X : Type} [TopologicalSpace X]

/-- **Inductive Hurewicz vanishing criterion (normalized cubical homology).** If `X` is path
connected with trivial `π_ 1 X x` and its integral normalized cubical homology vanishes in every
degree `n + 2`, then all homotopy groups `π_ k X x` are trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex (x : X)
    [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    (hH : ∀ n : ℕ,
      IsZero (((normalizedCubicalChainComplex ℤ).obj (TopCat.of X)).homology (n + 2)))
    (k : ℕ) : Subsingleton (π_ k X x) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).mp inferInstance
    | 1 => exact inferInstance
    | n + 2 =>
      let hHomology : Subsingleton
          (((normalizedCubicalChainComplex ℤ).obj (TopCat.of X)).homology (n + 2)) :=
        ModuleCat.subsingleton_of_isZero (hH n)
      exact (Additive.ofMul.trans (cubicalHurewiczAddEquiv ih).toEquiv).subsingleton_congr.mpr
        hHomology

end TauCeti
