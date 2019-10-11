#! /usr/bin/env python
# -*- coding: utf-8 -*-
import os


BASE_DIR = os.path.dirname(os.path.realpath(__file__))

if __name__ == "__main__":
    from driver.main import main
    main(BASE_DIR)
    
