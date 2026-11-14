/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Cubical.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.HomotopyClass
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction
public import TauCeti.AlgebraicTopology.Singular.Cubical.Coefficients
public import TauCeti.Topology.Homotopy.HomotopyGroup.Basic

/-!
# The cubical Hurewicz isomorphism

Let `X` be `(m - 1)`-connected at `x`, in the sense that `πₖ(X, x)` is trivial for every
`k < m`. Eilenberg's coherent deformation retracts the normalized cubical chains of `X` onto
the chains spanned by `m`-based cubes. In degree `m`, these cubes are precisely generalized
loops. The face relation identifies the resulting quotient by boundaries with `πₘ(X, x)`.

This file carries out that last step when `m ≥ 2`, in any universe `u`, by working over any
coefficient ring `R : Type u` isomorphic to `ℤ`: retraction onto based cubes proves surjectivity,
while transporting chains along `R ≃+* ℤ` and applying the based-cube class map to a bounding chain
proves injectivity. Specializing to `ℤ` in `Type 0` and to `ULift.{u} ℤ` in `Type u` packages the
resulting bijections as additive equivalences (`HomotopyGroup.cubicalHurewiczAddEquiv` and
`HomotopyGroup.cubicalHurewiczUliftAddEquiv`).

The inductive Hurewicz criteria
`TauCeti.subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex`,
`TauCeti.subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex_ulift_of_le`,
and `TauCeti.subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex_ulift`
show that a simply connected space with vanishing integral normalized cubical homology in degrees at
least two (up to `k`, or in every degree) has trivial homotopy groups in that range.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407--447.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.32.
-/

public section

noncomputable section

open CategoryTheory TauCeti
open scoped unitInterval Topology Topology.Homotopy

universe u

namespace HomotopyGroup

section RingEquiv

variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ} {R : Type u} [Ring R]

private abbrev K (R : Type u) [Ring R] (X : Type u) [TopologicalSpace X] :=
  (normalizedCubicalChainComplex R).obj (TopCat.of X)

private abbrev chainEquiv (R : Type u) [Ring R] : (K R X).X n ≃ₗ[R] NormalizedCubicalChain X R n :=
  normalizedCubicalChainComplexXEquiv (TopCat.of X) n

private abbrev chainOf (g : NormalizedCubicalChain X R n) : (K R X).X n :=
  (chainEquiv R).symm g

private abbrev chainTo (g : (K R X).X n) : NormalizedCubicalChain X R n :=
  chainEquiv R g

private theorem chainTo_chainOf (g : NormalizedCubicalChain X R n) :
    chainTo (chainOf g) = g :=
  (chainEquiv R).apply_symm_apply g

private theorem chainOf_chainTo (g : (K R X).X n) :
    chainOf (chainTo g) = g :=
  (chainEquiv R).symm_apply_apply g

private theorem zsmul_eq_smul (e : R ≃+* ℤ) {M : Type*} [AddCommGroup M] [Module R M]
    (r : R) (m : M) : e r • m = r • m := by
  have hr : ((e r : ℤ) : R) = r := e.injective (by simp)
  rw [← Int.cast_smul_eq_zsmul R, hr]

private def basedClassHomOfRingEquiv (x : X) (n : ℕ) (e : R ≃+* ℤ) :
    NormalizedCubicalChain X R (n + 2) →+ Additive (HomotopyGroup (Fin (n + 2)) X x) :=
  (NormalizedCubicalChain.basedClassHom x n).toAddMonoidHom.comp
    (NormalizedCubicalChain.mapRingHom X (↑e : R →+* ℤ) (n + 2)).toAddMonoidHom

private theorem basedClassHomOfRingEquiv_ofCube (e : R ≃+* ℤ) (c : SingularCube X (n + 2)) :
    basedClassHomOfRingEquiv x n e (NormalizedCubicalChain.ofCube X R c) =
      NormalizedCubicalChain.basedClassHom x n (NormalizedCubicalChain.ofCube X ℤ c) := by
  simp [basedClassHomOfRingEquiv]

private theorem basedClassHomOfRingEquiv_smul (e : R ≃+* ℤ) (r : R)
    (g : NormalizedCubicalChain X R (n + 2)) :
    basedClassHomOfRingEquiv x n e (r • g) = e r • basedClassHomOfRingEquiv x n e g := by
  simp [basedClassHomOfRingEquiv]

private theorem boundary_eq_zero_of_mem_basedSpan
    {g : NormalizedCubicalChain X R (n + 2)}
    (hg : g ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x})) :
    NormalizedCubicalChain.boundary X R (n + 1) g = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨c, hc, rfl⟩ := hg
      let p : Ω^ (Fin (n + 2)) X x :=
        ⟨c, SingularCube.isBased_iff_mem_genLoop.1 hc⟩
      exact GenLoop.boundary_ofCube_eq_zero R p
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul r a _ ha => simp [ha]

private def basedCycle (g : NormalizedCubicalChain X R (n + 2))
    (hg : g ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x})) :
    (K R X).cycles (n + 2) :=
  (K R X).moduleCatCyclesMk (chainOf g) (n + 1) (by simp)
    (by
      apply (chainEquiv R).injective
      calc
        chainTo ((K R X).d (n + 2) (n + 1) (chainOf g)) =
            NormalizedCubicalChain.boundary X R (n + 1) (chainTo (chainOf g)) :=
          normalizedCubicalChainComplexXEquiv_d_apply (TopCat.of X) (n + 1) (chainOf g)
        _ = NormalizedCubicalChain.boundary X R (n + 1) g := by rw [chainTo_chainOf]
        _ = 0 := boundary_eq_zero_of_mem_basedSpan hg
        _ = chainTo 0 := (map_zero (chainEquiv R)).symm)

private theorem iCycles_basedCycle (g : NormalizedCubicalChain X R (n + 2))
    (hg : g ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x})) :
    chainTo ((K R X).iCycles (n + 2) (basedCycle g hg)) = g := by
  calc
    chainTo ((K R X).iCycles (n + 2) (basedCycle g hg)) = chainTo (chainOf g) :=
      congrArg chainTo ((K R X).iCycles_moduleCatCyclesMk (n + 2) (chainOf g)
        (n + 1) (by simp) _)
    _ = g := chainTo_chainOf g

private theorem basedCycle_add
    (a b : NormalizedCubicalChain X R (n + 2))
    (ha : a ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x}))
    (hb : b ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x})) :
    basedCycle (a + b) (Submodule.add_mem _ ha hb) = basedCycle a ha + basedCycle b hb := by
  apply (K R X).moduleCat_iCycles_injective
  apply (chainEquiv R).injective
  simp only [map_add, iCycles_basedCycle]

private theorem basedCycle_smul (e : R ≃+* ℤ)
    (r : R) (a : NormalizedCubicalChain X R (n + 2))
    (ha : a ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x})) :
    basedCycle (r • a) (Submodule.smul_mem _ r ha) = r • basedCycle a ha := by
  rw [← zsmul_eq_smul e r (basedCycle a ha)]
  apply (K R X).moduleCat_iCycles_injective
  apply (chainEquiv R).injective
  simp only [map_zsmul, iCycles_basedCycle]
  exact (zsmul_eq_smul e r a).symm

/-- The cubical Hurewicz homomorphism sends the class of a generalized loop to the cubical
Hurewicz class of that loop. -/
private theorem cubicalHurewiczHom_ofMul_mk (R : Type u) [Ring R] (p : Ω^ (Fin (n + 2)) X x) :
    cubicalHurewiczHom R (n + 1)
        (Additive.ofMul (α := HomotopyGroup (Fin (n + 2)) X x) ⟦p⟧) =
      GenLoop.cubicalHurewicz R p :=
  -- `toMul_ofMul` cannot be used by `rw` here: `⟦p⟧` is elaborated at the quotient type
  -- underlying `HomotopyGroup`, so the step is the definitional equation `toMul (ofMul a) = a`.
  (cubicalHurewiczHom_apply R (n + 1) _).trans (cubicalHurewicz_mk R (n + 1) p)

private theorem cubicalHurewiczHom_basedClassHomOfRingEquiv (e : R ≃+* ℤ)
    (g : NormalizedCubicalChain X R (n + 2))
    (hg : g ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x})) :
    cubicalHurewiczHom R (n + 1) (basedClassHomOfRingEquiv x n e g) =
      (K R X).homologyπ (n + 2) (basedCycle g hg) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨c, hc, rfl⟩ := hg
      let p : Ω^ (Fin (n + 2)) X x :=
        ⟨c, SingularCube.isBased_iff_mem_genLoop.1 hc⟩
      have hbc : basedClassHomOfRingEquiv x n e (NormalizedCubicalChain.ofCube X R c) =
          Additive.ofMul (α := HomotopyGroup (Fin (n + 2)) X x) ⟦p⟧ := by
        rw [basedClassHomOfRingEquiv_ofCube]
        simpa only [p] using NormalizedCubicalChain.basedClassHom_ofCube_of_isBased hc
      rw [hbc, cubicalHurewiczHom_ofMul_mk]
      exact (GenLoop.homologyπ_eq_cubicalHurewicz R p (by
        apply (@chainEquiv X _ (n + 2) R _).injective
        calc
          chainTo ((K R X).iCycles (n + 2)
              (basedCycle (NormalizedCubicalChain.ofCube X R c)
                (Submodule.subset_span ⟨c, hc, rfl⟩))) =
              NormalizedCubicalChain.ofCube X R c :=
            iCycles_basedCycle _ _
          _ = chainTo (chainOf (NormalizedCubicalChain.ofCube X R c)) :=
            (chainTo_chainOf _).symm)).symm
  | zero =>
      have hzero : (0 : NormalizedCubicalChain X R (n + 2)) ∈ Submodule.span R
          (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x}) :=
        Submodule.zero_mem _
      have hz : basedCycle (x := x) (0 : NormalizedCubicalChain X R (n + 2)) hzero = 0 := by
        apply (K R X).moduleCat_iCycles_injective
        rw [map_zero]
        apply (chainEquiv R).injective
        exact (iCycles_basedCycle 0 hzero).trans (map_zero (chainEquiv R)).symm
      simp [hz]
  | add a b ha hb hha hhb =>
      rw [map_add, map_add, hha, hhb, basedCycle_add a b ha hb]
      exact (map_add _ _ _).symm
  | smul r a ha hha =>
      rw [basedClassHomOfRingEquiv_smul, map_zsmul, hha, basedCycle_smul e r a ha,
        ← zsmul_eq_smul e r (basedCycle a ha)]
      exact (map_zsmul _ _ _).symm

private theorem cubicalHurewiczHom_surjective (e : R ≃+* ℤ)
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Function.Surjective (cubicalHurewiczHom (X := X) (x := x) R (n + 1)) := by
  intro a
  obtain ⟨z, rfl⟩ := (K R X).moduleCat_homologyπ_surjective (n + 2) a
  let D := basedCubeDeformation hX
  let g : NormalizedCubicalChain X R (n + 2) :=
    D.retractChain R (n + 2) (chainTo ((K R X).iCycles (n + 2) z))
  have hg : g ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x}) :=
    D.retractChain_mem_span R _
  refine ⟨basedClassHomOfRingEquiv x n e g, ?_⟩
  rw [cubicalHurewiczHom_basedClassHomOfRingEquiv e g hg]
  have hcycle : basedCycle g hg =
      HomologicalComplex.cyclesMap (D.retractChainMap R) (n + 2) z := by
    apply (K R X).moduleCat_iCycles_injective
    apply (chainEquiv R).injective
    refine (iCycles_basedCycle g hg).trans ?_
    rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
    exact (D.normalizedCubicalChainComplexXEquiv_retractChainMap_f_apply R (n + 2)
      ((K R X).iCycles (n + 2) z)).symm
  rw [hcycle]
  calc
    (K R X).homologyπ (n + 2)
        (HomologicalComplex.cyclesMap (D.retractChainMap R) (n + 2) z) =
        HomologicalComplex.homologyMap (D.retractChainMap R) (n + 2)
          ((K R X).homologyπ (n + 2) z) := by
            simpa only [ModuleCat.comp_apply] using
              (ConcreteCategory.congr_hom
                (HomologicalComplex.homologyπ_naturality (D.retractChainMap R) (n + 2)) z).symm
    _ = (K R X).homologyπ (n + 2) z := by
      have hm := Homotopy.homologyMap_eq
        (BasedCubeDeformation.retractHomotopy (X := TopCat.of X) (n := n + 2) (x := x) D R)
        (n + 2)
      simpa only [HomologicalComplex.homologyMap_id, ModuleCat.id_apply] using
        (ConcreteCategory.congr_hom hm ((K R X).homologyπ (n + 2) z)).symm

/-- A based chain that is the cycle underlying a boundary in the complex `K R X` is the boundary
of the corresponding normalized cubical chain. -/
private theorem boundary_chainTo_eq_of_toCycles_eq
    {g : NormalizedCubicalChain X R (n + 2)}
    (hg : g ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x}))
    {b : (K R X).X (n + 3)} (hb : (K R X).toCycles (n + 3) (n + 2) b = basedCycle g hg) :
    NormalizedCubicalChain.boundary X R (n + 2) (chainTo b) = g := by
  have hi := congrArg (fun z ↦ (K R X).iCycles (n + 2) z) hb
  have hi' := congrArg chainTo hi
  calc
    NormalizedCubicalChain.boundary X R (n + 2) (chainTo b) =
        chainTo ((K R X).d (n + 3) (n + 2) b) :=
      (normalizedCubicalChainComplexXEquiv_d_apply (TopCat.of X) (n + 2) b).symm
    _ = chainTo ((K R X).iCycles (n + 2)
          ((K R X).toCycles (n + 3) (n + 2) b)) := by
      exact congrArg chainTo
        (ConcreteCategory.congr_hom
          (HomologicalComplex.toCycles_i (K R X) (n + 3) (n + 2)) b).symm
    _ = g := hi'.trans (iCycles_basedCycle g hg)

/-- If the dimensions below `n + 2` have trivial homotopy groups, a based cube whose chain is a
boundary has trivial based class. -/
private theorem basedClassHom_ofCube_eq_zero_of_boundary_eq (e : R ≃+* ℤ)
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    {c : SingularCube X (n + 2)} (hp : SingularCube.IsBased (n + 2) x c)
    {b : (K R X).X (n + 3)}
    (hboundary : NormalizedCubicalChain.boundary X R (n + 2) (chainTo b) =
      NormalizedCubicalChain.ofCube X R c) :
    NormalizedCubicalChain.basedClassHom x n (NormalizedCubicalChain.ofCube X ℤ c) = 0 := by
  let D := basedCubeDeformation hX
  have hret : NormalizedCubicalChain.boundary X R (n + 2)
      (D.retractChain R (n + 3) (chainTo b)) = NormalizedCubicalChain.ofCube X R c := by
    rw [D.boundary_retractChain, hboundary, D.retractChain_ofCube, D.retract_of_isBased hp]
  rw [← basedClassHomOfRingEquiv_ofCube e, ← hret]
  simp only [basedClassHomOfRingEquiv, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    NormalizedCubicalChain.mapRingHom_boundary]
  exact NormalizedCubicalChain.basedClassHom_boundary_of_mem_span
    (NormalizedCubicalChain.mapRingHom_mem_span_ofCube (↑e : R →+* ℤ)
      (D.retractChain_mem_span R (chainTo b)))

private theorem cubicalHurewiczHom_injective (e : R ≃+* ℤ)
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Function.Injective (cubicalHurewiczHom (X := X) (x := x) R (n + 1)) := by
  suffices hzero : ∀ a, cubicalHurewiczHom R (n + 1) a = 0 → a = 0 by
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
      let g := NormalizedCubicalChain.ofCube X R p'.1
      have hg : g ∈ Submodule.span R
          (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased (n + 2) x}) :=
        Submodule.subset_span ⟨p', hp, rfl⟩
      rw [← GenLoop.homologyπ_eq_cubicalHurewicz R p' (by
        apply (@chainEquiv X _ (n + 2) R _).injective
        exact (iCycles_basedCycle g hg).trans (chainTo_chainOf g).symm)] at ha
      obtain ⟨b, hb⟩ := ((K R X).moduleCat_homologyπ_eq_zero_iff (m := n + 3) (by simp)
        (basedCycle g hg)).1 ha
      have hclass := basedClassHom_ofCube_eq_zero_of_boundary_eq e hX hp
        (boundary_chainTo_eq_of_toCycles_eq hg hb)
      simpa only [NormalizedCubicalChain.basedClassHom_ofCube,
        SingularCube.basedClass_coe, p'] using hclass

end RingEquiv

section Small

variable {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}

/-- **The cubical Hurewicz isomorphism.** If `πₖ(X, x)` is trivial for every `k < n + 2`, then
the degree-`n + 2` cubical Hurewicz homomorphism is an additive equivalence from `π_{n+2}(X, x)`
to normalized cubical homology. -/
def cubicalHurewiczAddEquiv
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Additive (HomotopyGroup (Fin (n + 2)) X x) ≃+
      ((normalizedCubicalChainComplex ℤ).obj (TopCat.of X)).homology (n + 2) :=
  AddEquiv.ofBijective (cubicalHurewiczHom ℤ (n + 1))
    ⟨cubicalHurewiczHom_injective (RingEquiv.refl ℤ) hX,
      cubicalHurewiczHom_surjective (RingEquiv.refl ℤ) hX⟩

/-- The cubical Hurewicz equivalence has the cubical Hurewicz homomorphism as its forward map. -/
@[simp]
theorem cubicalHurewiczAddEquiv_apply
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    cubicalHurewiczAddEquiv hX a = cubicalHurewiczHom ℤ (n + 1) a :=
  AddEquiv.ofBijective_apply _ _ _

end Small

section Universe

variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

/-- **The cubical Hurewicz isomorphism in an arbitrary universe.** If `πₖ(X, x)` is trivial for
every `k < n + 2`, then the degree-`n + 2` cubical Hurewicz homomorphism with coefficients in
`ULift.{u} ℤ` is an additive equivalence from `π_{n+2}(X, x)` to normalized cubical homology. -/
def cubicalHurewiczUliftAddEquiv
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Additive (HomotopyGroup (Fin (n + 2)) X x) ≃+
      ((normalizedCubicalChainComplex (ULift.{u} ℤ)).obj (TopCat.of X)).homology (n + 2) :=
  AddEquiv.ofBijective (cubicalHurewiczHom (ULift.{u} ℤ) (n + 1))
    ⟨cubicalHurewiczHom_injective ULift.ringEquiv hX,
      cubicalHurewiczHom_surjective ULift.ringEquiv hX⟩

/-- `HomotopyGroup.cubicalHurewiczUliftAddEquiv` has the cubical Hurewicz homomorphism over
`ULift.{u} ℤ` as its forward map. -/
@[simp]
theorem cubicalHurewiczUliftAddEquiv_apply
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    cubicalHurewiczUliftAddEquiv hX a = cubicalHurewiczHom (ULift.{u} ℤ) (n + 1) a :=
  AddEquiv.ofBijective_apply _ _ _

end Universe

end HomotopyGroup

namespace TauCeti

open HomotopyGroup CategoryTheory.Limits

private theorem subsingleton_homotopyGroup_of_isZero_homology_of_ringEquiv
    {X : Type u} [TopologicalSpace X] {R : Type u} [Ring R] (e : R ≃+* ℤ) (x : X)
    [PathConnectedSpace X] [Subsingleton (π_ 1 X x)] {k : ℕ}
    (hH : ∀ n, n + 2 ≤ k →
      IsZero (((normalizedCubicalChainComplex R).obj (TopCat.of X)).homology (n + 2))) :
    Subsingleton (π_ k X x) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 => exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).mp inferInstance
    | 1 => exact inferInstance
    | n + 2 =>
      have := ModuleCat.subsingleton_of_isZero (hH n le_rfl)
      exact ((cubicalHurewiczHom_injective e fun m hm ↦
        ih m hm fun j hj ↦ hH j (hj.trans hm.le)).comp Additive.ofMul.injective).subsingleton

/-- **Inductive Hurewicz vanishing criterion up to `k` (normalized cubical homology, arbitrary
universe).** If `X : Type u` is path connected with trivial `π_ 1 X x` and its normalized cubical
homology over `ULift.{u} ℤ` vanishes in every degree `n + 2 ≤ k`, then `π_ k X x` is trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex_ulift_of_le
    {X : Type u} [TopologicalSpace X] (x : X) [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    {k : ℕ}
    (hH : ∀ n, n + 2 ≤ k →
      IsZero (((normalizedCubicalChainComplex (ULift.{u} ℤ)).obj (TopCat.of X)).homology (n + 2))) :
    Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_homology_of_ringEquiv ULift.ringEquiv x hH

/-- **Inductive Hurewicz vanishing criterion (normalized cubical homology, arbitrary universe).**
If `X : Type u` is path connected with trivial `π_ 1 X x` and its normalized cubical homology over
`ULift.{u} ℤ` vanishes in every degree `n + 2`, then all homotopy groups `π_ k X x` are trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex_ulift
    {X : Type u} [TopologicalSpace X] (x : X) [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    (hH : ∀ n : ℕ,
      IsZero (((normalizedCubicalChainComplex (ULift.{u} ℤ)).obj (TopCat.of X)).homology (n + 2)))
    (k : ℕ) : Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex_ulift_of_le x
    fun n _ ↦ hH n

/-- **Inductive Hurewicz vanishing criterion (normalized cubical homology).** If `X` is path
connected with trivial `π_ 1 X x` and its integral normalized cubical homology vanishes in every
degree `n + 2`, then all homotopy groups `π_ k X x` are trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex
    {X : Type} [TopologicalSpace X] (x : X)
    [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    (hH : ∀ n : ℕ,
      IsZero (((normalizedCubicalChainComplex ℤ).obj (TopCat.of X)).homology (n + 2)))
    (k : ℕ) : Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_homology_of_ringEquiv (RingEquiv.refl ℤ) x fun n _ ↦ hH n

end TauCeti
