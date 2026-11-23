/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Category.FrobeniusModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite free covers of linearized Frobenius modules

A finite module with invertible Frobenius linearization admits an equivariant surjection from
one whose underlying module is finite free. The scalar endomorphism need not be invertible or flat.

An arbitrary free cover need not admit a lift with invertible linearization on the same carrier.
Instead, identify the scalar extension of the free module with itself via a basis, and lift both
the linearization and its inverse to maps `b` and `a` on the free module. On two copies of the free
module, use the isomorphism `(x,y) ↦ (b (x − a y) + y, x − a y)`. The correction `1 − b a` on the
second summand of the first component is killed by the projection to the original module.

If the target is projective, the underlying surjection splits. Extension of scalars preserves
this split kernel sequence, so the kernel inherits an invertible linearization. The splitting
is only a splitting of the underlying modules.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Lemma 1.5.2 and
  Corollary 1.5.3, with the correction in *Relative p-adic Hodge theory, II: Imperfect period
  rings*, Appendix A.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti.FrobeniusModuleCat

variable {S : Type u} [CommRing S] {σ : S →+* S}

/-- Double a projective cover identified with its scalar extension to lift the linearization. -/
private theorem exists_biprod_linearization (M : FrobeniusModuleCat σ)
    {P : ModuleCat.{u} S} [Projective P] (q : P ⟶ M.carrier) [Epi q]
    (e : (ModuleCat.extendScalars σ).obj P ≅ P) :
    ∃ L : (ModuleCat.extendScalars σ).obj (P ⊞ P) ≅ P ⊞ P,
      (ModuleCat.extendScalars σ).map (biprod.desc q 0) ≫ M.linearization.hom =
        L.hom ≫ biprod.desc q 0 := by
  let F := ModuleCat.extendScalars σ
  have : PreservesBinaryBiproducts (ModuleCat.extendScalars σ : ModuleCat.{u} S ⥤ _) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let a := Projective.factorThru (q ≫ M.linearization.inv) (F.map q) ≫ e.hom
  let b := Projective.factorThru (e.inv ≫ F.map q ≫ M.linearization.hom) q
  have hb : b ≫ q = e.inv ≫ F.map q ≫ M.linearization.hom := Projective.factorThru_comp _ _
  have hab : a ≫ b ≫ q = q := by simp [a, hb]
  let d : P ⊞ P ≅ P ⊞ P :=
    Biprod.unipotentLower (-a) ≪≫ biprod.braiding P P ≪≫ Biprod.unipotentLower b
  have hq (g : P ⟶ M.carrier) : biprod.desc g (0 : P ⟶ M.carrier) = biprod.fst ≫ g := by
    simp [biprod.desc_eq]
  have hd : d.hom ≫ biprod.desc q 0 = biprod.desc (b ≫ q) 0 := by
    rw [hq]
    apply biprod.hom_ext' <;>
      simp [d, biprod.braiding, reassoc_of% Biprod.ofComponents_fst,
        reassoc_of% Biprod.ofComponents_snd, Preadditive.comp_add, Preadditive.add_comp, hab]
  refine ⟨(F.mapBiprod P P ≪≫ biprod.mapIso e e) ≪≫ d, ?_⟩
  -- Both sides factor through the first projection of the scalar-extended biproduct.
  rw [Iso.trans_hom, Category.assoc, hd]
  simp [hq, hb, F]

/-- Every finite linearized Frobenius module admits an equivariant surjection from a finite free
linearized Frobenius module. Surjectivity concerns the underlying module map. -/
theorem exists_finite_free_cover (M : FrobeniusModuleCat σ) [Module.Finite S M.carrier] :
    ∃ (P : FrobeniusModuleCat σ) (q : P ⟶ M),
      Module.Free S P.carrier ∧ Module.Finite S P.carrier ∧ Function.Surjective q.hom.f := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' S M.carrier
  let P := ModuleCat.of S (Fin n → S)
  let f : P ⟶ M.carrier := ModuleCat.ofHom q
  have : Epi f := (ModuleCat.epi_iff_surjective f).2 hq
  have : Projective P := ModuleCat.projective_of_free (Pi.basisFun S (Fin n))
  let F := ModuleCat.extendScalars σ
  let U : ModuleCat.{u} S := ModuleCat.of S S
  let i : (⨁ fun _ : Fin n ↦ U) ≅ P := ModuleCat.biproductIsoPi _
  let eP : F.obj P ≅ P := F.mapIso i.symm ≪≫ F.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ (tensorUnit σ).linearization) ≪≫ i
  obtain ⟨L, hL⟩ := exists_biprod_linearization M f eP
  let e := (ModuleCat.biprodIsoProd P P).toLinearEquiv
  let Q : FrobeniusModuleCat σ := ⟨P ⊞ P, L⟩
  have hsurj : Function.Surjective (biprod.desc f (0 : P ⟶ M.carrier)) := by
    apply (ModuleCat.epi_iff_surjective _).mp
    exact epi_of_epi_fac (biprod.inl_desc f 0)
  exact ⟨Q, homMk (biprod.desc f 0) hL, Module.Free.of_equiv e.symm,
    Module.Finite.equiv e.symm, by simpa only [homMk_hom_f] using hsurj⟩

/-- The kernel of an equivariant surjection of finite projective linearized Frobenius modules
inherits an invertible linearization and is finite projective. The resulting sequence splits
on underlying modules. -/
theorem exists_finite_projective_kernel_of_surjective {P M : FrobeniusModuleCat σ}
    [Module.Finite S P.carrier] [Module.Projective S P.carrier] [Module.Projective S M.carrier]
    (q : P ⟶ M) (hq : Function.Surjective q.hom.f) :
    ∃ (N : FrobeniusModuleCat σ) (i : N ⟶ P) (w : i.hom.f ≫ q.hom.f = 0),
      Module.Finite S N.carrier ∧ Module.Projective S N.carrier ∧
        Nonempty (ShortComplex.mk i.hom.f q.hom.f w).Splitting := by
  let f := q.hom.f
  let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hg : Epi f := (ModuleCat.epi_iff_surjective f).2 hq
  have : Epi T.g := hg
  have : Projective T.X₃ := (inferInstance : Projective M.carrier)
  have hT : T.ShortExact := ⟨ShortComplex.kernelSequence_exact f⟩
  let s := hT.splittingOfProjective
  let F := ModuleCat.extendScalars σ
  -- Tensoring preserves this splitting, even if the endomorphism is not flat.
  let h := (s.map F).fIsKernel
  let e := h.conePointUniqueUpToIso (kernelIsKernel (F.map f))
  let k := kernel.mapIso (F.map f) f P.linearization M.linearization
    (map_hom_f_comp_linearization_hom q)
  let N : FrobeniusModuleCat σ := ⟨kernel f, e ≪≫ k⟩
  have hi : (e ≪≫ k).hom ≫ kernel.ι f = F.map (kernel.ι f) ≫ P.linearization.hom := by
    simpa [k, e, T, Category.assoc] using congrArg (· ≫ P.linearization.hom)
      (h.conePointUniqueUpToIso_hom_comp (kernelIsKernel (F.map f)) WalkingParallelPair.zero)
  let i : N ⟶ P := homMk (kernel.ι f) hi.symm
  have hi' : i.hom.f = kernel.ι f := homMk_hom_f _ _
  have hr : Function.Surjective s.r.hom := by
    have : IsSplitEpi s.r := ⟨⟨T.f, s.f_r⟩⟩
    exact (ModuleCat.epi_iff_surjective s.r).1 inferInstance
  have : Module.Finite S T.X₂ := (inferInstance : Module.Finite S P.carrier)
  have : Module.Projective S T.X₂ := (inferInstance : Module.Projective S P.carrier)
  refine ⟨N, i, by simp [hi', f], Module.Finite.of_surjective s.r.hom hr, ?_, ?_⟩
  · exact Module.Projective.of_split T.f.hom s.r.hom (congrArg ModuleCat.Hom.hom s.f_r)
  · simpa only [hi'] using (⟨s⟩ : Nonempty T.Splitting)

end TauCeti.FrobeniusModuleCat
