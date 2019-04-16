#ifndef TESTFPU_H
#define TESTFPU_H
#include <QCoreApplication>
#include <QtTest/QtTest>

// hi bi-51
class TestFPU : public QObject {
  Q_OBJECT
 private slots:
  void testMul();
  void testDiv();
  void testSub();
  void testAdd();
  void testSin();
  void testCos();
};
#endif  // TESTFPU_H
